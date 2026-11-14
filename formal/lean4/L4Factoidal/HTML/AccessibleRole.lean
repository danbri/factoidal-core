/-
L4Factoidal.HTML.AccessibleRole — the computed role of an element for assistive technology:
the first valid token of its `role` attribute (WAI-ARIA 1.2 §7.1, "role attribute", with the
conflict resolution of `none`/`presentation` §9.1 and the landmarks that need a name), else
its implicit role from HTML-AAM's element mappings.

The roles are the ones `test_driver.get_computed_role` answers (WebDriver "Get Computed
Role"): lower case, `image` for `img`, `none` for `presentation`, `generic` for the
elements HTML-AAM maps to it, "" for an element with no role.

It is a function of the tree; the accessibility tree that a host builds from it can use the
same function.
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.HTML.AccessibleRole
open L4Factoidal.DOM L4Factoidal.DOM.Forms

/-- The non-abstract roles of WAI-ARIA 1.2 and the ARIA 1.3 roles browsers have, that an
author may give. -/
def ariaRoles : List String :=
  ["alert", "alertdialog", "application", "article", "banner", "blockquote", "button", "caption",
   "cell", "checkbox", "code", "columnheader", "combobox", "comment", "complementary",
   "contentinfo", "definition", "deletion", "dialog", "document", "emphasis", "feed", "figure",
   "form", "generic", "grid", "gridcell", "group", "heading", "image", "img", "insertion", "link",
   "list", "listbox", "listitem", "log", "main", "mark", "marquee", "math", "menu", "menubar",
   "menuitem", "menuitemcheckbox", "menuitemradio", "meter", "navigation", "none", "note",
   "option", "paragraph", "presentation", "progressbar", "radio", "radiogroup", "region", "row",
   "rowgroup", "rowheader", "scrollbar", "search", "searchbox", "separator", "slider",
   "spinbutton", "status", "strong", "subscript", "suggestion", "superscript", "switch", "tab",
   "table", "tablist", "tabpanel", "term", "textbox", "time", "timer", "toolbar", "tooltip",
   "tree", "treegrid", "treeitem"]

/-- The roles a computation answers besides "": the author roles after `normalize`, and the
implicit roles. -/
def answerRoles : List String := ariaRoles ++ ["graphics-document"]

def lowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
def asciiLower (s : String) : String := s.map lowerChar
def isAsciiWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'

/-- The tokens of a `role` attribute, split on ASCII whitespace, in ASCII lower case. -/
def tokens (v : String) : List String :=
  let step := fun (st : List String × List Char) (c : Char) =>
    if isAsciiWs c then (if st.2.isEmpty then st else (st.1 ++ [asciiLower (String.ofList st.2.reverse)], []))
    else (st.1, c :: st.2)
  let (acc, cur) := v.toList.foldl step ([], [])
  if cur.isEmpty then acc else acc ++ [asciiLower (String.ofList cur.reverse)]

/-- One name for synonyms: `img` is `image`, `presentation` is `none`. -/
def normalize (t : String) : String :=
  if t == "img" then "image" else if t == "presentation" then "none" else t

def attr? (d : Dom) (k : NodeId) (name : String) : Option String :=
  ((d.get k).attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

def nonEmpty (o : Option String) : Bool := match o with
  | some v => !(v.trimAscii.toString.isEmpty)
  | none => false

/-- Whether the author gave the element a name (`aria-label`, `aria-labelledby`, `title`):
the landmarks `region` and `form` are only those with one. -/
def named (d : Dom) (k : NodeId) : Bool :=
  nonEmpty (attr? d k "aria-label") || nonEmpty (attr? d k "aria-labelledby") || nonEmpty (attr? d k "title")

/-- The global ARIA attributes (WAI-ARIA 1.2 §6.4): one of them on an element keeps it from
being presentational. -/
def globalAria : List String :=
  ["aria-atomic", "aria-busy", "aria-controls", "aria-current", "aria-describedby",
   "aria-description", "aria-details", "aria-dropeffect", "aria-flowto", "aria-grabbed",
   "aria-keyshortcuts", "aria-label", "aria-labelledby", "aria-live", "aria-owns",
   "aria-relevant", "aria-roledescription", "aria-braillelabel", "aria-brailleroledescription"]

/-- An element that can take the focus (an approximation of HTML's focusable areas by markup:
a `tabindex`, a link, a form control that is not disabled, a `summary`, an editing host). -/
def focusable (d : Dom) (k : NodeId) : Bool :=
  (attr? d k "tabindex").isSome ||
  (isHtml d k ["a", "area"] && (attr? d k "href").isSome) ||
  (isHtml d k ["button", "select", "textarea"] && (attr? d k "disabled").isNone) ||
  (isHtml d k ["input"] && (attr? d k "disabled").isNone && asciiLower ((attr? d k "type").getD "") != "hidden") ||
  isHtml d k ["summary"] ||
  (match (attr? d k "contenteditable").map asciiLower with
   | some "" | some "true" | some "plaintext-only" => true
   | _ => false)

/-- The author's role: the first token that is a role the element may have. -/
def explicitRole (d : Dom) (k : NodeId) : Option String :=
  match attr? d k "role" with
  | none => none
  | some v => (tokens v).findSome? fun t =>
      if !(ariaRoles.contains t) then none
      else if (t == "region" || t == "form") && !named d k then none
      else if (t == "none" || t == "presentation") &&
          (focusable d k || (d.get k).attrs.any (fun a => a.ns.isNone && globalAria.contains a.lname)) then none
      else some (normalize t)

def hasAncestor (d : Dom) (k : NodeId) (names : List String) : Bool := Id.run do
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p =>
      if isHtml d p names then return true
      cur := (d.get p).parent
  return false

/-- The role of an `input` by its type (HTML-AAM §4 "input"). -/
def inputRole (d : Dom) (k : NodeId) : String :=
  let list := (attr? d k "list").isSome
  match asciiLower ((attr? d k "type").getD "text") with
  | "button" | "image" | "reset" | "submit" => "button"
  | "checkbox" => "checkbox"
  | "radio" => "radio"
  | "range" => "slider"
  | "number" => "spinbutton"
  | "search" => if list then "combobox" else "searchbox"
  | "email" | "tel" | "text" | "url" => if list then "combobox" else "textbox"
  | "color" | "date" | "datetime-local" | "month" | "time" | "week" | "file" | "hidden" | "password" => ""
  | _ => if list then "combobox" else "textbox"

/-- A `th`: a row header when its scope says so or it begins a row of data cells, else a
column header (HTML-AAM `th`, the table's header model simplified). -/
def thRole (d : Dom) (k : NodeId) : String :=
  match (attr? d k "scope").map asciiLower with
  | some "row" | some "rowgroup" => "rowheader"
  | some "col" | some "colgroup" => "columnheader"
  | _ =>
    match (d.get k).parent with
    | some r =>
      let cells := (d.get r).kids.toList.filter fun c => isHtml d c ["td", "th"]
      if hasAncestor d k ["thead"] then "columnheader"
      else if cells.head? == some k && cells.any (isHtml d · ["td"]) then "rowheader"
      else "columnheader"
    | none => "columnheader"

/-- The implicit role of an HTML element (HTML-AAM §4, "HTML element role mappings"). -/
def implicitRole (d : Dom) (k : NodeId) : String :=
  let x := d.get k
  if x.type != .element then "" else
  if x.ns == some svgNS then (if x.lname == "svg" then "graphics-document" else "") else
  if x.ns != some htmlNS then "" else
  match x.lname with
  | "a" | "area" => if (attr? d k "href").isSome then "link" else "generic"
  | "address" | "details" | "fieldset" | "hgroup" | "optgroup" => "group"
  | "article" => "article"
  | "aside" => "complementary"
  | "b" | "bdi" | "bdo" | "body" | "data" | "div" | "i" | "pre" | "q" | "samp" | "small" | "span" | "u" => "generic"
  | "blockquote" => "blockquote"
  | "button" => "button"
  | "caption" => "caption"
  | "code" => "code"
  | "datalist" => "listbox"
  | "dd" => "definition"
  | "del" | "s" => "deletion"
  | "dfn" | "dt" => "term"
  | "dialog" => "dialog"
  | "em" => "emphasis"
  | "figure" => "figure"
  | "footer" => if hasAncestor d k ["article", "aside", "main", "nav", "section"] then "generic" else "contentinfo"
  | "header" => if hasAncestor d k ["article", "aside", "main", "nav", "section"] then "generic" else "banner"
  | "form" => if named d k then "form" else "generic"
  | "h1" | "h2" | "h3" | "h4" | "h5" | "h6" => "heading"
  | "hr" => "separator"
  | "html" => "document"
  | "img" => if attr? d k "alt" == some "" then "none" else "image"
  | "input" => inputRole d k
  | "ins" => "insertion"
  | "li" => "listitem"
  | "main" => "main"
  | "mark" => "mark"
  | "math" => "math"
  | "menu" | "ol" | "ul" => "list"
  | "meter" => "meter"
  | "nav" => "navigation"
  | "option" => "option"
  | "output" => "status"
  | "p" => "paragraph"
  | "progress" => "progressbar"
  | "search" => "search"
  | "section" => if named d k then "region" else "generic"
  | "select" =>
    if (attr? d k "multiple").isSome || ((attr? d k "size").bind (·.trimAscii.toString.toNat?)).any (· > 1) then "listbox"
    else "combobox"
  | "strong" => "strong"
  | "sub" => "subscript"
  | "sup" => "superscript"
  | "table" => "table"
  | "tbody" | "tfoot" | "thead" => "rowgroup"
  | "td" => "cell"
  | "th" => thRole d k
  | "textarea" => "textbox"
  | "time" => "time"
  | "tr" => "row"
  | _ => ""

/-- The computed role: the author's, else the implicit one. -/
def computedRole (d : Dom) (k : NodeId) : String :=
  (explicitRole d k).getD (implicitRole d k)

/-! ## What is proved -/

theorem normalize_mem (t : String) (h : t ∈ ariaRoles) : normalize t ∈ answerRoles := by
  unfold normalize answerRoles
  by_cases h1 : (t == "img") = true
  · simp only [h1, if_true]; simp [ariaRoles]
  · by_cases h2 : (t == "presentation") = true
    · simp only [h1, h2, if_true, Bool.false_eq_true, if_false]; simp [ariaRoles]
    · simp only [h1, h2, Bool.false_eq_true, if_false]
      exact List.mem_append_left _ h

/-- Says: an author's role that is answered is a role of WAI-ARIA (an invalid token, an
abstract role or a misspelling is never answered). -/
theorem explicitRole_valid (d : Dom) (k : NodeId) (r : String) (h : explicitRole d k = some r) :
    r ∈ answerRoles := by
  unfold explicitRole at h
  split at h
  · cases h
  · obtain ⟨t, _, ht⟩ := List.exists_of_findSome?_eq_some h
    split at ht
    · cases ht
    · split at ht
      · cases ht
      · split at ht
        · cases ht
        · rename_i hm _ _
          cases ht
          exact normalize_mem t (by simpa using hm)

/-- Says: a `role` of only invalid tokens leaves the implicit role. -/
theorem invalid_tokens_implicit (d : Dom) (k : NodeId) (v : String) (hv : attr? d k "role" = some v)
    (h : ∀ t ∈ tokens v, ariaRoles.contains t = false) : computedRole d k = implicitRole d k := by
  unfold computedRole explicitRole
  rw [hv]
  have : (tokens v).findSome? (fun t =>
      if !(ariaRoles.contains t) then none
      else if (t == "region" || t == "form") && !named d k then none
      else if (t == "none" || t == "presentation") &&
          (focusable d k || (d.get k).attrs.any (fun a => a.ns.isNone && globalAria.contains a.lname)) then none
      else some (normalize t)) = none := by
    rw [List.findSome?_eq_none_iff]
    intro t ht
    have hc := h t ht
    simp only [hc, Bool.not_false, ↓reduceIte]
  simp only []
  rw [this]
  rfl

/-! ## Tests (html-aam/roles.html, wai-aria/role/fallback-roles.html) -/

#guard tokens " Foo\tBUTTON  link " == ["foo", "button", "link"] && tokens "" == [] && tokens "\u2800 button" == ["\u2800", "button"]
#guard normalize "img" == "image" && normalize "presentation" == "none" && normalize "link" == "link"

private def roleOf (html tag : String) : String :=
  let d := DOM.parseHtmlDocument html
  match (List.range d.size).find? (fun i => (d.get i).lname == tag) with
  | some i => computedRole d i
  | none => "?"

#guard roleOf "<a href=#>x</a>" "a" == "link" && roleOf "<a>x</a>" "a" == "generic"
#guard roleOf "<div role='foo button'>x</div>" "div" == "button" && roleOf "<div role='foo'>x</div>" "div" == "generic"
#guard roleOf "<div role='region group'>x</div>" "div" == "group" && roleOf "<div role='ReGiOn group' aria-label=x>x</div>" "div" == "region"
#guard roleOf "<img alt=''>" "img" == "none" && roleOf "<img alt=x>" "img" == "image" && roleOf "<div role=img>x</div>" "div" == "image"
#guard roleOf "<button role=presentation>x</button>" "button" == "button" && roleOf "<span role=presentation>x</span>" "span" == "none"
#guard roleOf "<span role=none aria-label=x>x</span>" "span" == "generic"
#guard roleOf "<select size=2></select>" "select" == "listbox" && roleOf "<select></select>" "select" == "combobox"
#guard roleOf "<input type=search list=l>" "input" == "combobox" && roleOf "<input>" "input" == "textbox" && roleOf "<input type=range>" "input" == "slider"
#guard roleOf "<table><tr><th>a</th><td>b</td></tr></table>" "th" == "rowheader" && roleOf "<table><thead><tr><th>a</th></tr></thead></table>" "th" == "columnheader"
#guard roleOf "<article><footer>x</footer></article>" "footer" == "generic" && roleOf "<footer>x</footer>" "footer" == "contentinfo"
#guard roleOf "<section>x</section>" "section" == "generic" && roleOf "<section title=t>x</section>" "section" == "region"
#guard roleOf "<abbr>x</abbr>" "abbr" == "" && roleOf "<h3>x</h3>" "h3" == "heading" && roleOf "<menu></menu>" "menu" == "list"

end L4Factoidal.HTML.AccessibleRole
