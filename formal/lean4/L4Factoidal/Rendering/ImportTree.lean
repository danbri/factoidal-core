/-
L4Factoidal.Rendering.ImportTree — the style sheets that a sheet imports, in the order they
apply, from the sheets a host has fetched; and the ones it has yet to fetch.

Source: CSS Cascade 5 §6.1 (`@import`: "the user agent must fetch the style sheet at the
given URL and treat its contents as if they were written in place of the `@import` rule",
under the rule's layer, `supports()` condition and media query list).

Before this module no `@import` was followed: the sheet reader left the rule out and no
host fetched its sheet. A page whose style sheet is a list of imports was drawn unstyled.

The engine names what to fetch and reads what is given; a host fetches. `walk` goes through
the imports of a sheet, depth first: an import whose sheet is given is read in place (its
own imports first, then its text, each under the conditions of every import rule on the way
to it); an import whose sheet is not given is listed as lacking. The module knows nothing
of CSS syntax: the imports of a text, the wrapper that puts a text under an import's
conditions, and URL resolution are parameters (`Edge`, `resolve`), so that it has no
dependency and its bounds are plain.

## Bounds (work a page drives)

* Each URL is taken once for a sheet, at its first import (`seen`): a cycle of imports
  ends, and sheets that import each other in every direction cost one visit each. (A sheet
  imported twice applies once, where CSS would apply it again at the second place: the
  order of its rules against the sheet that imported it second can differ.)
* At most `maxSheets` URLs are taken for one sheet; the rest are ignored.
* The chain of imports is followed `maxDepth` deep.
* `sheetsOf` and `lackingOf` answer at most `maxSheets` entries (`sheetsOf_length`,
  `lackingOf_length`).
-/

namespace L4Factoidal.Rendering.ImportTree

/-- One `@import` of a sheet: the URL as written, and the text of the imported sheet put
under the rule's conditions. -/
structure Edge where
  url : String
  wrap : String → String

/-- Most URLs taken for the imports of one sheet, at every depth together. -/
def maxSheets : Nat := 64

/-- The deepest chain of imports followed. -/
def maxDepth : Nat := 8

/-- What a walk has found: the URLs taken (newest first), the sheets to read, in the order
they apply, each with its URL, and the URLs whose sheets are not given. -/
structure Found where
  seen : List String := []
  sheets : List (String × String) := []
  lacking : List String := []

/-- The imports of `source`, a sheet at `base`, depth first. `edges` gives the imports of a
text, `resolve base url` the URL of an import written in a sheet at `base`, `given` the
text of a fetched sheet. `outer` puts a text under the conditions of the imports on the
way here. -/
def walk (edges : String → List Edge) (resolve : String → String → String) (given : String → Option String) :
    Nat → Found → (String → String) → String → String → Found
  | 0, found, _, _, _ => found
  | fuel+1, found, outer, base, source =>
    (edges source).foldl (fun found e =>
      let url := resolve base e.url
      if found.seen.contains url || found.seen.length ≥ maxSheets then found else
      match given url with
      | none => { found with seen := url :: found.seen, lacking := found.lacking ++ [url] }
      | some text =>
        let under := fun t => outer (e.wrap t)
        let inner := walk edges resolve given fuel { found with seen := url :: found.seen } under url text
        { inner with sheets := inner.sheets ++ [(url, under text)] }) found

/-- The sheets that the sheet `source` at `base` imports and that are given, in the order
they apply (all before `source` itself), each with its own URL. -/
def sheetsOf (edges : String → List Edge) (resolve : String → String → String) (given : String → Option String)
    (base source : String) : List (String × String) :=
  (walk edges resolve given maxDepth { seen := [base] } id base source).sheets.take maxSheets

/-- The URLs of the sheets that `source` imports, at any depth through the given sheets,
and that are not given: what a host fetches next. -/
def lackingOf (edges : String → List Edge) (resolve : String → String → String) (given : String → Option String)
    (base source : String) : List String :=
  (walk edges resolve given maxDepth { seen := [base] } id base source).lacking.take maxSheets

/-! ## Theorems -/

/-- Kind: resource bound. Says: at most `maxSheets` imported sheets are read for one sheet,
whatever the sheets say. Does not say: that the walk itself is short (it takes each URL
once and stops taking them at `maxSheets`; that is by construction and tested). -/
theorem sheetsOf_length (edges : String → List Edge) (resolve : String → String → String)
    (given : String → Option String) (base source : String) :
    (sheetsOf edges resolve given base source).length ≤ maxSheets := by
  unfold sheetsOf
  exact List.length_take_le _ _

/-- Kind: resource bound. Says: a host is asked for at most `maxSheets` sheets for one
sheet's imports in one answer. -/
theorem lackingOf_length (edges : String → List Edge) (resolve : String → String → String)
    (given : String → Option String) (base source : String) :
    (lackingOf edges resolve given base source).length ≤ maxSheets := by
  unfold lackingOf
  exact List.length_take_le _ _

/-- Kind: property. Says: a sheet with no `@import` reads nothing more and asks for
nothing: the walk leaves what it has found as it was. -/
theorem walk_no_imports (edges : String → List Edge) (resolve : String → String → String)
    (given : String → Option String) (fuel : Nat) (found : Found) (outer : String → String)
    (base source : String) (h : edges source = []) :
    walk edges resolve given fuel found outer base source = found := by
  cases fuel with
  | zero => rfl
  | succ n => simp [walk, h]

/-- Kind: property. Says: with no fuel nothing is followed. -/
theorem walk_zero (edges : String → List Edge) (resolve : String → String → String)
    (given : String → Option String) (found : Found) (outer : String → String) (base source : String) :
    walk edges resolve given 0 found outer base source = found := rfl

/-! ## Tests: sheets as lists of the names they import, `name` or `name!` (wrapped) -/

private def toyEdges (text : String) : List Edge :=
  (text.splitOn " ").filter (· != "") |>.filterMap fun w =>
    if w.startsWith "@" then
      let name := (w.drop 1).toString
      if name.endsWith "!" then some { url := (name.dropEnd 1).toString, wrap := fun t => "[" ++ t ++ "]" }
      else some { url := name, wrap := id }
    else none
private def toyResolve (_ : String) (url : String) : String := url
private def toyGiven (table : List (String × String)) (url : String) : Option String := table.lookup url

-- a imports b and c; b imports d: the order is d, b, c
#guard sheetsOf toyEdges toyResolve (toyGiven [("b", "@d B"), ("c", "C"), ("d", "D")]) "a" "@b @c A" ==
  [("d", "D"), ("b", "@d B"), ("c", "C")]
-- conditions nest: d is under b's wrapper too
#guard sheetsOf toyEdges toyResolve (toyGiven [("b", "@d! B"), ("d", "D")]) "a" "@b! A" ==
  [("d", "[[D]]"), ("b", "[@d! B]")]
-- what is not given is asked for, once, and nothing is read for it
#guard lackingOf toyEdges toyResolve (toyGiven [("b", "@d @e B")]) "a" "@b @c @c A" == ["d", "e", "c"]
#guard sheetsOf toyEdges toyResolve (toyGiven [("b", "@d @e B")]) "a" "@b @c A" == [("b", "@d @e B")]
-- a cycle ends: a imports b, b imports a and itself
#guard sheetsOf toyEdges toyResolve (toyGiven [("b", "@a @b B")]) "a" "@b A" == [("b", "@a @b B")]
#guard lackingOf toyEdges toyResolve (toyGiven [("b", "@a @b B")]) "a" "@b A" == []
-- a sheet imported twice is read once, at its first place
#guard sheetsOf toyEdges toyResolve (toyGiven [("b", "B"), ("c", "@b C")]) "a" "@b @c A" == [("b", "B"), ("c", "@b C")]
-- no import: nothing
#guard sheetsOf toyEdges toyResolve (toyGiven []) "a" "A" == [] && lackingOf toyEdges toyResolve (toyGiven []) "a" "A" == []
-- depth: a chain longer than maxDepth is cut
private def chain : List (String × String) := (List.range 20).map fun i => (s!"s{i}", s!"@s{i+1} S{i}")
#guard (sheetsOf toyEdges toyResolve (toyGiven chain) "a" "@s0 A").length == maxDepth
-- breadth: every sheet imports every other; each is read once, and at most maxSheets
private def mesh : List (String × String) :=
  (List.range 100).map fun i => (s!"m{i}", " ".intercalate ((List.range 100).map fun j => s!"@m{j}"))
#guard (sheetsOf toyEdges toyResolve (toyGiven mesh) "a" (" ".intercalate ((List.range 100).map fun j => s!"@m{j}"))).length ≤ maxSheets

end L4Factoidal.Rendering.ImportTree
