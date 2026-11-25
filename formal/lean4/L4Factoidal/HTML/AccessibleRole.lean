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
   "contentinfo", "definition", "deletion", "dialog", "directory", "document", "emphasis", "feed", "figure",
   "form", "generic", "grid", "gridcell", "group", "heading", "image", "img", "insertion", "link",
   "list", "listbox", "listitem", "log", "main", "mark", "marquee", "math", "menu", "menubar",
   "menuitem", "menuitemcheckbox", "menuitemradio", "meter", "navigation", "none", "note",
   "option", "paragraph", "presentation", "progressbar", "radio", "radiogroup", "region", "row",
   "rowgroup", "rowheader", "scrollbar", "search", "searchbox", "sectionfooter", "sectionheader", "separator", "slider",
   "spinbutton", "status", "strong", "subscript", "suggestion", "superscript", "switch", "tab",
   "table", "tablist", "tabpanel", "term", "textbox", "time", "timer", "toolbar", "tooltip",
   "tree", "treegrid", "treeitem",
   -- Digital Publishing WAI-ARIA 1.1 (DPUB-AAM: each answers itself)
   "doc-abstract", "doc-acknowledgments", "doc-afterword", "doc-appendix", "doc-backlink", "doc-biblioentry",
   "doc-bibliography", "doc-biblioref", "doc-chapter", "doc-colophon", "doc-conclusion", "doc-cover",
   "doc-credit", "doc-credits", "doc-dedication", "doc-endnote", "doc-endnotes", "doc-epigraph",
   "doc-epilogue", "doc-errata", "doc-example", "doc-footnote", "doc-foreword", "doc-glossary",
   "doc-glossref", "doc-index", "doc-introduction", "doc-noteref", "doc-notice", "doc-pagebreak",
   "doc-pagefooter", "doc-pageheader", "doc-pagelist", "doc-part", "doc-preface", "doc-prologue",
   "doc-pullquote", "doc-qna", "doc-subtitle", "doc-tip", "doc-toc",
   -- WAI-ARIA Graphics Module 1.0
   "graphics-document", "graphics-object", "graphics-symbol"]

/-- The roles a computation answers besides "": the author roles after `normalize`, and the
implicit roles. -/
def answerRoles : List String := ariaRoles

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

/-- The tokens of an ID reference list, split on ASCII whitespace (case kept). -/
def tokens' (v : String) : List String :=
  ((v.split isAsciiWs).toList.map (·.toString)).filter (· != "")

/-- One name for synonyms: `img` is `image`, `presentation` is `none`. -/
def normalize (t : String) : String :=
  if t == "img" then "image" else if t == "presentation" then "none" else if t == "directory" then "list" else t

def attr? (d : Dom) (k : NodeId) (name : String) : Option String :=
  ((d.get k).attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

def nonEmpty (o : Option String) : Bool := match o with
  | some v => !(v.trimAscii.toString.isEmpty)
  | none => false

/-- Whether the author gave the element a name (`aria-label`, `aria-labelledby`, `title`):
the landmarks `region` and `form` are only those with one. -/
def named (d : Dom) (k : NodeId) : Bool :=
  nonEmpty (attr? d k "aria-label") || nonEmpty (attr? d k "title") ||
  (match attr? d k "aria-labelledby" with
   | some ids =>
     -- an ID reference names the element only when an element with that ID is in its tree
     let wanted := ((ids.split isAsciiWs).toList.map (·.toString)).filter (· != "")
     !wanted.isEmpty && (d.treeOrder (d.root k)).any fun j =>
       (d.get j).type == .element && (match attr? d j "id" with | some id => wanted.contains id | none => false)
   | none => false)

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

/-- Whether an `li` is an item of a list: its nearest ancestor that is not a plain `div` or
`span` is a `ul`, `ol` or `menu` that keeps its list role, or an element the author gave
the role `list`. -/
def inList (d : Dom) (k : NodeId) : Bool := Id.run do
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p =>
      match attr? d p "role" with
      | some v =>
        -- the author's role of the ancestor decides
        return (tokens v).head? == some "list" || (tokens v).head? == some "directory"
      | none =>
        if isHtml d p ["ul", "ol", "menu"] then return true
        if !isHtml d p ["div", "span"] then return false
        cur := (d.get p).parent
  return false

/-- An SVG element's `href`: in no namespace or in XLink's. -/
def svgHref (d : Dom) (k : NodeId) : Bool :=
  (d.get k).attrs.any fun a => a.lname == "href"

/-- The first `title` child of an SVG element (SVG-AAM §8.1). -/
def svgTitle (d : Dom) (k : NodeId) : Option NodeId :=
  (d.get k).kids.toList.find? fun c => (d.get c).type == .element && (d.get c).ns == some svgNS && (d.get c).lname == "title"

/-- The implicit role of an SVG element (SVG-AAM §6.2, the elements with a mapping here):
the `svg` root, a link, a group or an image that has a name. -/
def svgRole (d : Dom) (k : NodeId) : String :=
  let x := d.get k
  let labelled := named d k || (svgTitle d k).isSome
  match x.lname with
  | "svg" => "graphics-document"
  | "a" => if svgHref d k then "link" else ""
  | "g" => if labelled then "group" else ""
  | "image" => if labelled then "image" else ""
  | _ => ""

/-- The role of an `input` by its type (HTML-AAM §4 "input"). -/
def inputRole (d : Dom) (k : NodeId) : String :=
  let list := (attr? d k "list").isSome
  match asciiLower ((attr? d k "type").getD "text") with
  | "button" | "image" | "reset" | "submit" => "button"
  | "checkbox" => if (attr? d k "switch").isSome then "switch" else "checkbox"
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

/-- An `img` (HTML-AAM `img`): `none` for an empty `alt` with no author name, and for an
image with no source and no name at all; an image with a source and no `alt` attribute is an
`image`; else `image`. -/
def imgRole (d : Dom) (k : NodeId) : String :=
  let blank := fun (o : Option String) => match o with | some v => v.trimAscii.toString.isEmpty | none => true
  let authorNamed := nonEmpty (attr? d k "aria-label") || nonEmpty (attr? d k "aria-labelledby")
  let sourced := nonEmpty (attr? d k "src") || nonEmpty (attr? d k "srcset")
  if attr? d k "alt" == some "" then (if authorNamed then "image" else "none")
  else if (attr? d k "alt").isNone && sourced then "image"
  else if blank (attr? d k "alt") && blank (attr? d k "title") && !authorNamed then "none"
  else "image"

/-- The implicit role of an HTML element (HTML-AAM §4, "HTML element role mappings"). -/
def implicitRole (d : Dom) (k : NodeId) : String :=
  let x := d.get k
  if x.type != .element then "" else
  if x.ns == some svgNS then svgRole d k else
  if x.ns != some htmlNS then "" else
  match x.lname with
  | "a" | "area" => if (attr? d k "href").isSome then "link" else "generic"
  | "address" | "details" | "fieldset" | "hgroup" | "optgroup" => "group"
  | "article" => "article"
  -- scoped to sectioning content and without a name: generic (HTML-AAM `aside`)
  | "aside" => if hasAncestor d k ["article", "aside", "nav", "section"] && !named d k then "generic" else "complementary"
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
  | "img" => imgRole d k
  | "input" => inputRole d k
  | "ins" => "insertion"
  | "li" => if inList d k then "listitem" else "generic"
  | "main" => "main"
  | "mark" => "mark"
  | "math" => "math"
  | "dir" | "menu" | "ol" | "ul" => "list"
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

/-! ## The accessible name (Accessible Name and Description Computation 1.2 §4.3, simplified)

The steps taken: hidden nodes give nothing unless a reference targets a hidden subtree; `aria-labelledby` (one level: not followed while computing a
referenced node); an embedded control's value while computing a name from content;
`aria-label`; the host language's label (HTML-AAM: button values, `alt`, the `label`
elements of a labelable control, `legend`, `figcaption`, `caption`, an SVG `title`); the
name from content for the roles that allow it and inside a name being computed from
content; the `title` and then the `placeholder`. Block elements are separated by spaces;
white space is collapsed. CSS visibility comes from the caller. CSS generated content is omitted. -/

/-- Roles whose name may come from their content (WAI-ARIA 1.2 §5.2.8.6). -/
def nameFromContentRoles : List String :=
  ["button", "cell", "checkbox", "columnheader", "gridcell", "heading", "link", "menuitem",
   "menuitemcheckbox", "menuitemradio", "option", "radio", "row", "rowheader", "sectionhead",
   "switch", "tab", "tooltip", "treeitem", "caption", "code", "deletion", "emphasis",
   "insertion", "paragraph", "strong", "subscript", "superscript", "term", "definition", "time", "mark"]

/-- HTML elements whose role allows a name from content in WAI-ARIA, and that browsers give
no name from their content (html-aam/accname-computation-by-element): their text is read as
content. -/
def noContentName (d : Dom) (k : NodeId) : Bool :=
  (attr? d k "role").isNone &&
    isHtml d k ["dfn", "code", "em", "mark", "s", "strong", "sub", "sup", "time", "td", "th", "tr"]

def blockTags : List String :=
  ["address", "article", "aside", "blockquote", "br", "dd", "details", "dialog", "div", "dl", "dt",
   "fieldset", "figcaption", "figure", "footer", "form", "h1", "h2", "h3", "h4", "h5", "h6",
   "header", "hgroup", "hr", "li", "main", "nav", "ol", "p", "pre", "section", "table", "td", "th",
   "tr", "ul", "caption", "summary", "legend", "option", "optgroup"]

private def nonNameElement (d : Dom) (k : NodeId) : Bool :=
  isHtml d k ["script", "style", "template", "noscript", "head", "title"]

def hiddenEl (d : Dom) (k : NodeId) : Bool :=
  let x := d.get k
  x.type == .element && ((attr? d k "hidden").isSome || (attr? d k "aria-hidden").map asciiLower == some "true" ||
    nonNameElement d k)

/-- The CSS facts used for a name. `displayed` is false for `display: none`.
`visible` is false for computed `visibility: hidden` or `collapse`. -/
structure NameStyle where
  displayed : NodeId → Bool := fun _ => true
  visible : NodeId → Bool := fun _ => true
  /-- WebDriver may query a native element whose renderer has no box of its own.
  Only the root step can ignore that display fact. -/
  allowUnboxedRoot : Bool := false

/-- A hidden element at the current step of the name computation. -/
def hiddenAt (d : Dom) (style : NameStyle) (k : NodeId) (allowUnboxed : Bool := false) : Bool :=
  hiddenEl d k || (!allowUnboxed && !style.displayed k) || !style.visible k

/-- Whether the root of an IDREF traversal is hidden. Display and ARIA hiding on an ancestor
hide the reference too. Computed CSS visibility is taken at the reference itself, since a
descendant can override its ancestor's visibility. -/
def hiddenReference (d : Dom) (style : NameStyle) (k : NodeId) : Bool :=
  !style.visible k || Id.run do
    let mut cur := k
    for _ in [0:d.size + 1] do
      if hiddenEl d cur || !style.displayed cur then return true
      match (d.get cur).parent with
      | none => return false
      | some p => cur := p
    return false

def collapse (s : String) : String :=
  " ".intercalate (((s.split isAsciiWs).toList.map (·.toString)).filter (· != ""))

def byIdIn (d : Dom) (k : NodeId) (id : String) : Option NodeId :=
  let root := d.root k
  (d.treeOrder root).find? fun j => (d.get j).type == .element && attr? d j "id" == some id

/-- The `label` elements of a labelable control: those whose `for` names its ID, and the
nearest ancestor `label` without `for`. -/
def labelsOf (d : Dom) (k : NodeId) : List NodeId :=
  let byFor := match attr? d k "id" with
    | some id => if id.isEmpty then [] else
        ((d.treeOrder (d.root k)).filter fun j => isHtml d j ["label"] && attr? d j "for" == some id).toList
    | none => []
  let ancestor := Id.run do
    let mut cur := (d.get k).parent
    for _ in [0:d.size + 1] do
      match cur with
      | none => return none
      | some p =>
        if isHtml d p ["label"] then return (if (attr? d p "for").isNone then some p else none)
        cur := (d.get p).parent
    return none
  -- a hidden `label` names nothing
  (byFor ++ (match ancestor with | some a => if byFor.contains a then [] else [a] | none => [])).filter fun l =>
    (attr? d l "hidden").isNone

/-- The first child with one of the tags that is not hidden (html-aam/hidden-names: a hidden
`caption` or `legend` names nothing). -/
def firstChildTag (d : Dom) (k : NodeId) (tags : List String) : Option NodeId :=
  (d.get k).kids.toList.find? fun c => isHtml d c tags && (attr? d c "hidden").isNone

/-- The value an embedded control gives a name computed from content (§4.3.2 step 2C). -/
def embeddedValue (d : Dom) (k : NodeId) : Option String :=
  if isHtml d k ["input"] then
    let t := asciiLower ((attr? d k "type").getD "text")
    if ["text", "search", "email", "tel", "url", "number", "range", ""].contains t then some (inputValue d k)
    else none
  else if isHtml d k ["select"] then
    let opts := (d.treeOrder k).filter (isHtml d · ["option"])
    let sel := (opts.toList.find? fun o => (attr? d o "selected").isSome) <|> opts.toList.head?
    some ((sel.bind fun o => d.textContent o).getD "")
  else if isHtml d k ["textarea"] then some ((d.textContent k).getD "")
  else match explicitRole d k with
    -- ARIA widgets: a text field's or combo box's text, a list box's selected options, a range's value
    | some "combobox" | some "textbox" | some "searchbox" => some ((d.textContent k).getD "")
    | some "listbox" =>
      let chosen := (d.treeOrder k false).toList.filter fun o =>
        explicitRole d o == some "option" && (attr? d o "aria-selected").map asciiLower == some "true"
      some (" ".intercalate (chosen.map fun o => (d.textContent o).getD ""))
    | some "slider" | some "spinbutton" | some "scrollbar" =>
      some ((attr? d k "aria-valuetext").getD ((attr? d k "aria-valuenow").getD ""))
    | _ => none

mutual
/-- The text alternative of node `k` (§4.3.2): `labelled` while computing a node that an
`aria-labelledby` or `aria-describedby` names, `content` while computing a name from the
content of an ancestor. `includeHidden` carries the exception for a hidden IDREF target
through its descendants. `fuel` bounds the depth (the tree's nesting). -/
def textAlternative (d : Dom) (fuel : Nat) (k : NodeId) (labelled content : Bool)
    (style : NameStyle := {}) (includeHidden : Bool := false) : String :=
  match fuel with
  | 0 => ""
  | fuel + 1 =>
    let x := d.get k
    if x.type == .text then x.data
    else if x.type != .element then ""
    else if hiddenAt d style k (!content && style.allowUnboxedRoot) &&
        !labelled && (!includeHidden || nonNameElement d k) then ""
    else
      let byLabelledBy := if labelled then "" else match attr? d k "aria-labelledby" with
        | some ids => collapse (" ".intercalate ((tokens' ids).filterMap fun id =>
            (byIdIn d k id).map fun j => textAlternative d fuel j true true style (hiddenReference d style j)))
        | none => ""
      if !byLabelledBy.isEmpty then byLabelledBy else
      let embedded := if content then embeddedValue d k else none
      match embedded with
      | some v => v
      | none =>
      let label := (attr? d k "aria-label").map (·.trimAscii.toString) |>.getD ""
      if !label.isEmpty then label else
      -- An explicitly empty area alternative is still the host-language alternative.
      if !labelled && !content && style.allowUnboxedRoot &&
          isHtml d k ["area"] && (attr? d k "alt").any (·.trimAscii.isEmpty) then "" else
      let native := hostLabel d fuel k style
      if !native.isEmpty then native else
      let role := computedRole d k
      let fromContent := if content || labelled || (nameFromContentRoles.contains role && !noContentName d k) ||
            isHtml d k ["summary"] then
          childrenText d fuel x.kids.toList style includeHidden else ""
      if !fromContent.isEmpty then fromContent else
      let title := (attr? d k "title").getD ""
      if !title.trimAscii.toString.isEmpty then title else
      let ph := (attr? d k "placeholder").getD ""
      if !ph.trimAscii.toString.isEmpty then ph else (attr? d k "aria-placeholder").getD ""

/-- The names of children in order, block elements set apart by spaces. -/
def childrenText (d : Dom) (fuel : Nat) (kids : List NodeId)
    (style : NameStyle := {}) (includeHidden : Bool := false) : String :=
  match kids with
  | [] => ""
  | c :: rest =>
    let t := textAlternative d fuel c false true style includeHidden
    let t := if isHtml d c blockTags then " " ++ t ++ " " else t
    t ++ childrenText d fuel rest style includeHidden

/-- The host language's label (HTML-AAM §5, accessible name computations by element). -/
def hostLabel (d : Dom) (fuel : Nat) (k : NodeId) (style : NameStyle := {}) : String :=
  let x := d.get k
  -- SVG-AAM §8.1: the `title` child, else a link's `xlink:title`
  if x.ns == some svgNS then
    (match svgTitle d k with
     | some t => (d.textContent t).getD ""
     | none => (((d.get k).attrs.find? fun a => a.lname == "title" && a.ns.isSome).map (·.value)).getD "")
  else if x.ns != some htmlNS then "" else
  -- the control itself is left out of its label's text
  let labels := fun (ls : List NodeId) => collapse (" ".intercalate (ls.map fun l =>
    childrenText d fuel ((d.get l).kids.toList.filter (· != k)) style))
  match x.lname with
  | "input" =>
    let t := asciiLower ((attr? d k "type").getD "text")
    let fromLabels := labels (labelsOf d k)
    if !fromLabels.isEmpty && ["button", "submit", "reset", "image"].contains t then fromLabels
    else if ["button", "submit", "reset"].contains t then
      match attr? d k "value" with
      | some v => v
      | none => if t == "submit" then "Submit" else if t == "reset" then "Reset" else labels (labelsOf d k)
    else if t == "image" then
      match attr? d k "alt" with
      | some v => if v.isEmpty then (attr? d k "value").getD "" else v
      | none => (attr? d k "value").getD ((attr? d k "title").getD "Submit")
    else labels (labelsOf d k)
  | "textarea" | "select" | "meter" | "progress" | "output" | "button" => labels (labelsOf d k)
  | "img" | "area" => (attr? d k "alt").getD ""
  | "fieldset" => match firstChildTag d k ["legend"] with
    | some l => collapse (childrenText d fuel (d.get l).kids.toList style)
    | none => ""
  | "figure" => match firstChildTag d k ["figcaption"] with
    | some l => collapse (childrenText d fuel (d.get l).kids.toList style)
    | none => ""
  | "table" => match firstChildTag d k ["caption"] with
    | some l => collapse (childrenText d fuel (d.get l).kids.toList style)
    | none => ""
  | "optgroup" => (attr? d k "label").getD ""
  | _ => ""
end

/-- The accessible name of element `k`, white space collapsed. -/
def accessibleName (d : Dom) (k : NodeId) (style : NameStyle := {}) : String :=
  collapse (textAlternative d (d.size + 1) k false false style)

/-! ## What is proved -/

theorem normalize_mem (t : String) (h : t ∈ ariaRoles) : normalize t ∈ answerRoles := by
  unfold normalize answerRoles
  by_cases h1 : (t == "img") = true
  · simp only [h1, if_true]; simp [ariaRoles]
  · by_cases h2 : (t == "presentation") = true
    · simp only [h1, h2, if_true, Bool.false_eq_true, if_false]; simp [ariaRoles]
    · by_cases h3 : (t == "directory") = true
      · simp only [h1, h2, h3, if_true, Bool.false_eq_true, if_false]; simp [ariaRoles]
      · simp only [h1, h2, h3, Bool.false_eq_true, if_false]
        exact h

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

/-- Says: a hidden element that no `aria-labelledby` names gives no text to any name. -/
theorem hidden_no_name (d : Dom) (k : NodeId) (fuel : Nat) (content : Bool)
    (he : (d.get k).type = .element) (hh : hiddenEl d k = true) :
    textAlternative d (fuel + 1) k false content = "" := by
  simp [textAlternative, hiddenAt, he, hh]
  intro h
  exact absurd h (by decide)

/-! ## Tests (html-aam/roles.html, wai-aria/role/fallback-roles.html) -/

#guard tokens " Foo\tBUTTON  link " == ["foo", "button", "link"] && tokens "" == [] && tokens "\u2800 button" == ["\u2800", "button"]
#guard normalize "img" == "image" && normalize "presentation" == "none" && normalize "link" == "link" && normalize "directory" == "list"

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

private def nameOf (html tag : String) : String :=
  let d := DOM.parseHtmlDocument html
  match (List.range d.size).find? (fun i => (d.get i).lname == tag) with
  | some i => accessibleName d i
  | none => "?"

#guard nameOf "<div role=button aria-label=' label '>x</div>" "div" == "label"
#guard nameOf "<button>Save <b>all</b></button>" "button" == "Save all"

-- CSS facts distinguish a hidden reference root from hidden descendants of a visible root.
private def nameWithHiddenSpans (referenceHidden : Bool) : String :=
  let d := DOM.parseHtmlDocument
    "<button aria-labelledby=ref></button><span id=ref>Open <span id=child>details</span></span>"
  let style : NameStyle :=
    { displayed := fun k => attr? d k "id" != some "child"
      visible := fun k => !referenceHidden || attr? d k "id" != some "ref" }
  let k := (d.treeOrder 0).find? (isHtml d · ["button"])
  (k.map fun i => accessibleName d i style).getD "?"

-- The exception is only for the starting element's display, not a child's
-- display, the root's explicit hiding, or its visibility.
private def nameAtUnboxedRoot (html : String) (visible allowUnboxedRoot : Bool) : String :=
  let d := DOM.parseHtmlDocument html
  match (d.treeOrder 0).find? (isHtml d · ["button"]) with
  | some k => accessibleName d k {displayed := fun n => n != k && attr? d n "id" != some "child",
                                  visible := fun n => n != k || visible, allowUnboxedRoot}
  | none => "?"

#guard nameAtUnboxedRoot "<button>Open<span id=child> hidden</span></button>" true true == "Open"
#guard nameAtUnboxedRoot "<button>Open</button>" true false == ""
#guard nameAtUnboxedRoot "<button>Open</button>" false true == ""
#guard nameAtUnboxedRoot "<button aria-hidden=true>Open</button>" true true == ""
#guard nameAtUnboxedRoot "<button hidden>Open</button>" true true == ""
#guard nameAtUnboxedRoot "<area alt='' title=Fallback>" true true == ""
#guard nameAtUnboxedRoot "<area alt='' title=Fallback aria-label=Label>" true true == "Label"
#guard nameAtUnboxedRoot "<area title=Fallback>" true true == "Fallback"

#guard nameWithHiddenSpans false == "Open"
#guard nameWithHiddenSpans true == "Open details"
#guard nameOf "<span id=a>first</span><span id=b>second</span><div role=link aria-labelledby='a b'>x</div>" "div" == "first second"
#guard nameOf "<label for=i>Name</label><input id=i>" "input" == "Name" && nameOf "<label>Mail <input></label>" "input" == "Mail"
#guard nameOf "<img alt='a cat'>" "img" == "a cat" && nameOf "<input type=submit>" "input" == "Submit"
#guard nameOf "<div title=tip>x</div>" "div" == "tip" && nameOf "<input placeholder=search>" "input" == "search"
#guard nameOf "<a href=#><div>one</div><div>two</div></a>" "a" == "one two"
#guard nameOf "<a href=#>x<span hidden>y</span></a>" "a" == "x"
#guard nameOf "<fieldset><legend>Group</legend></fieldset>" "fieldset" == "Group"
#guard roleOf "<img>" "img" == "none" && roleOf "<img alt='' aria-label=x>" "img" == "image" && roleOf "<img src=a.png alt=' '>" "img" == "none"
#guard roleOf "<input type=checkbox switch>" "input" == "switch" && roleOf "<div><li>x</li></div>" "li" == "generic"
#guard roleOf "<ul><div><li>x</li></div></ul>" "li" == "listitem" && roleOf "<div role=list><li>x</li></div>" "li" == "listitem"
#guard roleOf "<ul role=none><li>x</li></ul>" "li" == "generic" && roleOf "<ul><li>x</li></ul>" "li" == "listitem"
#guard roleOf "<div role=doc-chapter>x</div>" "div" == "doc-chapter" && roleOf "<div role=graphics-symbol>x</div>" "div" == "graphics-symbol"
#guard roleOf "<img src=a.png>" "img" == "image" && roleOf "<img srcset=a.png>" "img" == "image" && roleOf "<dir></dir>" "dir" == "list"
#guard roleOf "<section aria-labelledby=nowhere>x</section>" "section" == "generic" && roleOf "<p id=t>t</p><section aria-labelledby=t>x</section>" "section" == "region"
#guard roleOf "<svg><a href='#'>x</a></svg>" "a" == "link" && roleOf "<svg><g aria-label=l></g></svg>" "g" == "group" && roleOf "<svg><g></g></svg>" "g" == ""
#guard nameOf "<svg><circle><title>dot</title></circle></svg>" "circle" == "dot" && nameOf "<svg><title>pic</title></svg>" "svg" == "pic"
#guard nameOf "<em title=t>x</em>" "em" == "t" && nameOf "<code>x</code>" "code" == "" && nameOf "<table><tr><td>x</td></tr></table>" "td" == ""
#guard nameOf "<details><summary title=t>sum</summary></details>" "summary" == "sum"
#guard nameOf "<label><input type=checkbox> Flash <span role=slider aria-valuenow=3 aria-label=n></span> times</label>" "input" == "Flash 3 times"
#guard nameOf "<label><input type=checkbox> Pick <ul role=listbox aria-label=n><li role=option>1</li><li role=option aria-selected=true>2</li></ul> now</label>" "input" == "Pick 2 now"
#guard nameOf "<label><input type=checkbox> Do <span role=combobox aria-label=n>3</span> times</label>" "input" == "Do 3 times"
#guard nameOf "<label for=i hidden>H</label><input id=i>" "input" == "" && nameOf "<fieldset><legend hidden>H</legend><legend>V</legend></fieldset>" "fieldset" == "V"
#guard nameOf "<a href=x><em>very</em> good</a>" "a" == "very good" && nameOf "<div role=cell>x</div>" "div" == "x"
#guard roleOf "<article><aside>x</aside></article>" "aside" == "generic" && roleOf "<aside>x</aside>" "aside" == "complementary"
#guard nameOf "<label for=b>Go</label><input id=b type=submit value=v>" "input" == "Go" && nameOf "<input type=submit value=v>" "input" == "v"
#guard nameOf "<input aria-placeholder=ap value=v>" "input" == "ap"


end L4Factoidal.HTML.AccessibleRole
