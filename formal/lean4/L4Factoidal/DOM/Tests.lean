/-
L4Factoidal.DOM.Tests — `#guard` checks of the DOM arena, checked when this
module is built. They cover `moveBefore` (the "move" algorithm, DOM §4.2.3),
which the jsdom differential (`tests/dom/diff.mjs`) cannot check: jsdom 30.1.3
has no `moveBefore`. Each expected result is read from the steps of the
algorithm in whatwg/dom `3c53f93a`.
-/
import L4Factoidal.DOM.OfHtml
import L4Factoidal.DOM.Selectors
import L4Factoidal.DOM.Forms

namespace L4Factoidal.DOM.Tests

open L4Factoidal.DOM

/-- The first element in tree order with local name `nm`. -/
def el (d : Dom) (nm : String) : NodeId :=
  ((d.treeOrder 0).find? fun k => (d.get k).type == .element && (d.get k).lname == nm).getD 0

def kidNames (d : Dom) (p : NodeId) : List String :=
  (d.get p).kids.toList.map fun k => let x := d.get k; if x.type == .text then "#" ++ x.data else x.lname

def doc0 : Dom := parseHtmlDocument "<!DOCTYPE html><body><p>a<i>i</i></p><b>x</b>t</body>"

def errOf : Res Unit → Option DomError
  | (_, .error e) => some e
  | (_, .ok _) => none

/-- The arena after an operation that must not throw. -/
def okOf : Res Unit → Option Dom
  | (d, .ok ()) => some d
  | (_, .error _) => none

-- move: `b` before `p` within body; the arena stays well-formed
#guard (okOf (doc0.move (el doc0 "b") (el doc0 "body") (some (el doc0 "p")))).map
  (fun d => (kidNames d (el d "body"), d.wellFormed)) == some (["b", "p", "#t"], true)
-- move: a node to the end of a new parent in the same tree
#guard (okOf (doc0.move (el doc0 "b") (el doc0 "p") none)).map
  (fun d => (kidNames d (el d "p"), kidNames d (el d "body"))) == some (["#a", "i", "b"], ["p", "#t"])
-- move: child is the node itself: the reference child is its next sibling (no change)
#guard (okOf (doc0.move (el doc0 "b") (el doc0 "body") (some (el doc0 "b")))).map
  (fun d => kidNames d (el d "body")) == some ["p", "b", "#t"]
-- step 1: a node of another root (a new element) cannot be moved
#guard (match doc0.createElement 0 "span" with
  | (d, .ok s) => errOf (d.move s (el d "body") none)
  | (_, .error _) => none) == some .hierarchyRequest
-- step 2: a node cannot be moved into its own descendant
#guard errOf (doc0.move (el doc0 "p") (el doc0 "i") none) == some .hierarchyRequest
-- step 3: the reference child must be a child of the new parent
#guard errOf (doc0.move (el doc0 "b") (el doc0 "body") (some (el doc0 "i"))) == some .notFound
-- step 4: a doctype is not an Element or CharacterData node
#guard errOf (doc0.move ((doc0.get 0).kids[0]!) (el doc0 "body") none) == some .hierarchyRequest
-- step 5: a Text node cannot be moved into a document
#guard errOf (doc0.move ((doc0.get (el doc0 "body")).kids[2]!) 0 none) == some .hierarchyRequest
-- step 6: the document has an element child already
#guard errOf (doc0.move (el doc0 "b") 0 none) == some .hierarchyRequest

def tpl : Dom := parseHtmlDocument "<template><p>x</p></template>"
-- a template element cannot go into its own template contents: the contents'
-- host is the element, so it is a host-including inclusive ancestor (DOM §4.2.2)
#guard errOf (tpl.appendChild ((tpl.get (el tpl "template")).content.getD 0) (el tpl "template")) ==
  some .hierarchyRequest
-- the parser's template children are the children of the contents fragment
#guard kidNames tpl ((tpl.get (el tpl "template")).content.getD 0) == ["p"] && tpl.wellFormed
-- a deep clone of a template element clones its contents
#guard (let (d, c) := tpl.cloneNode (el tpl "template") true
  kidNames d ((d.get c).content.getD 0)) == ["p"]

/-! ## Namespaces (DOM §1.4 "validate and extract", §4.4 "locate a namespace") -/

/-- "Validate and extract", with the error as a value. -/
def vae (ns : Option String) (q : String) (attr : Bool := false) :
    DomError ⊕ (Option String × Option String × String) :=
  match Dom.validateAndExtract ns q attr with
  | .ok r => .inr r
  | .error e => .inl e
-- the prefix is what comes before the first ":"; the local name is all the rest
#guard vae (some "http://example.com/") "f:o:o" == .inr (some "http://example.com/", some "f", "o:o")
#guard vae (some "") "foo" == .inr (none, none, "foo")
#guard vae none "f:oo" == .inl .namespace
#guard vae (some "http://example.com/") "xml:foo" == .inl .namespace
#guard vae (some xmlNS) "xml:foo" == .inr (some xmlNS, some "xml", "foo")
#guard vae (some "http://example.com/") "xmlns" == .inl .namespace
#guard vae (some xmlnsNS) "foo" == .inl .namespace
#guard vae (some xmlnsNS) "xmlns:foo" true == .inr (some xmlnsNS, some "xmlns", "foo")
#guard vae (some "http://example.com/") ":foo" == .inl .invalidCharacter
#guard vae (some "http://example.com/") "f:" == .inl .invalidCharacter
#guard vae none "0" true == .inr (none, none, "0")
#guard vae none "0" == .inl .invalidCharacter

def nsDoc : Dom := parseHtmlDocument "<body><p><i>x</i></p></body>"
def nsDoc1 : Dom :=
  let d := nsDoc
  let d := (d.setAttributeNS (el d "p") (some xmlnsNS) "xmlns:a" "urnA").1
  (d.setAttributeNS (el d "p") (some xmlnsNS) "xmlns" "urnD").1
-- a declaration on an ancestor; the HTML namespace of the element itself
#guard nsDoc1.lookupNamespaceURI (el nsDoc1 "i") (some "a") == some "urnA"
#guard nsDoc1.lookupNamespaceURI (el nsDoc1 "p") none == some htmlNS
#guard nsDoc1.lookupNamespaceURI (el nsDoc1 "i") (some "xml") == some xmlNS
#guard nsDoc1.lookupNamespaceURI 0 none == some htmlNS
#guard nsDoc1.lookupPrefix (el nsDoc1 "i") (some "urnA") == some "a"
#guard nsDoc1.lookupPrefix (el nsDoc1 "i") (some "") == none
-- setAttributeNS keeps the prefix of an existing attribute; removeAttributeNS by local name
#guard (let d := (nsDoc1.setAttributeNS (el nsDoc1 "p") (some xmlnsNS) "xmlns:a" "urnB").1
  (d.getAttributeNS? (el d "p") (some xmlnsNS) "a", (d.get (el d "p")).attrs.size)) == (some "urnB", 2)
#guard (nsDoc1.removeAttributeNS (el nsDoc1 "p") (some xmlnsNS) "a").getAttributeNS? (el nsDoc1 "p") (some xmlnsNS) "a" == none

/-! ## Other documents: `importNode` (a clone into a document) and `graft` -/

-- a deep clone into another document: every node of the copy is in that document
#guard (let (d, other) := (doc0.push { type := .document, htmlDoc := true })
  let d := d.setNode other fun n => { n with doc := other }
  let (d, c) := d.cloneNode (el d "p") true (some other)
  (d.treeOrder c).toList.all fun k => (d.get k).doc == other) == true
-- a grafted document keeps its shape, moved past the old nodes
#guard (let (d, root) := doc0.graft tpl
  (root == doc0.size, d.size == doc0.size + tpl.size, (d.get root).type == .document,
    kidNames d ((d.get (root + el tpl "template")).content.getD 0))) == (true, true, true, ["p"])

/-! ## Selectors (DOM.Selectors) -/

def selDoc : Dom := parseHtmlDocument
  "<body><ul id=u><li class='a b'>1</li><li lang=en-GB>2</li><li id=t3 align=Center>3</li></ul><p>x</p></body>"
def qsa (sel : String) : Option (List String) :=
  (Selectors.parse sel).map fun l => (Selectors.querySelectorAll selDoc 0 l).toList.map fun k =>
    (((selDoc.get k).attrs.find? (·.lname == "id")).map (·.value)).getD (selDoc.get k).lname
#guard qsa "li.a" == some ["li"]
#guard qsa "ul > li:nth-child(2n+1)" == some ["li", "t3"]
#guard qsa "li:not(.a):lang(en)" == some ["li"]
#guard qsa "[align=center]" == some ["t3"]
#guard qsa "#u ~ p, li:last-child" == some ["t3", "p"]
#guard qsa "body > li" == some []
#guard qsa "li + #t3" == some ["t3"]
#guard qsa "#\\74 3" == some ["t3"]
#guard qsa "*|li:is(#t3)" == some ["t3"]
#guard (["", "div,", ".5cm", "ns|div", ":example", ">*", "[*=test]", "div::example"].map Selectors.parse).all (·.isNone)

/-! ## Examples: `:has()`, pseudo-elements, input states, `:dir()` (Selectors 4) -/

def exDoc : Dom := parseHtmlDocument
  ("<body><div id=a class=x><p id=p1><img id=i1></p><span id=s1></span><span id=s2 class=y></span></div>" ++
   "<div id=b><h2 id=h>t</h2><input id=in1 required placeholder=x><input id=in2 readonly><textarea id=ta></textarea>" ++
   "<details id=d open></details><p id=r dir=rtl><b id=rb>x</b></p><p id=au dir=auto>\u05d0</p></div></body>")
def exIds (sel : String) : Option (List String) :=
  (Selectors.parse sel).map fun l => (Selectors.querySelectorAll exDoc 0 l).toList.map fun k =>
    (((exDoc.get k).attrs.find? (·.lname == "id")).map (·.value)).getD (exDoc.get k).lname
-- :has(): descendant, child, next sibling, later sibling; lists; nesting in :not() and :is()
#guard exIds "div:has(img)" == some ["a"]
#guard exIds "div:has(> img)" == some []
#guard exIds "p:has(> img)" == some ["p1"]
#guard exIds ":has(> p > img)" == some ["a"]
#guard exIds "p:has(+ span)" == some ["p1"]
#guard exIds "p:has(+ .y)" == some []
#guard exIds "p:has(~ .y)" == some ["p1"]
#guard exIds "#a :has(~ span)" == some ["p1", "s1"]
#guard exIds "div:has(h2, img)" == some ["a", "b"]
#guard exIds "div:not(:has(img))" == some ["b"]
-- :has() is not valid in :has() (Selectors 4 §4.5)
#guard exIds "div:has(p:has(img))" == none
#guard exIds "div:has(.x img)" == some []
#guard exIds "body:has(.x img) > #b" == some ["b"]
#guard exIds "div:has(+ div h2)" == some ["a"]
#guard exIds ":is(div, p):has(> span.y)" == some ["a"]
-- input states from attributes, :heading, :dir()
#guard exIds ":required" == some ["in1"]
#guard exIds "input:optional" == some ["in2"]
#guard exIds "#b :read-write" == some ["in1", "ta"]
#guard exIds "input:read-only" == some ["in2"]
#guard exIds ":placeholder-shown" == some ["in1"]
#guard exIds ":open" == some ["d"]
#guard exIds ":heading" == some ["h"]
#guard exIds ":heading(2, 3)" == some ["h"]
#guard exIds ":heading(1)" == some []
#guard exIds "#b :dir(rtl)" == some ["r", "rb", "au"]
#guard exIds "#b > :dir(ltr)" == some ["h", "in1", "in2", "ta", "d"]
-- pseudo-elements are valid and match no element; what may follow one
#guard (["::selection", "a::placeholder", "li::marker", "::backdrop", "::-webkit-scrollbar", "::part(a b)",
  "::part(foo):hover", "::part(foo)::before", "::view-transition", "::view-transition-group(*)",
  "::view-transition-old(name.cls):only-child", "::-webkit-scrollbar-thumb:horizontal", "a::before:hover",
  ":is(::before)", "::slotted(p)", "::highlight(x)"].map exIds).all (· == some [])
#guard (["::no-such", "::before.a", "::before div", "::part()", "::part(0)", "::part('a')", "::part(a):first-child",
  "::part(a):has(b)", ":not(::before)", ":has(::before)", "::view-transition:hover", "::view-transition(x)",
  "::view-transition-group()", "::view-transition-group(*.*)", "::view-transition-group(a. b)",
  "::view-transition-new(default)", "::view-transition-old(a):hover", "::selection:first-child",
  ":has()", ":heading()", ":heading(a)", ":no-such-class"].map Selectors.parse).all (·.isNone)
-- ::scroll-button() and :host()
#guard (["::scroll-button(up)", "::scroll-button( * )", "::scroll-button(block-end):focus", ":host(:is(div))", ":host(.a)",
  ":host-context(div)"].map Selectors.parse).all (·.isSome)
#guard (["::scroll-button(foo)", "::scroll-button()", ":host(div .foo)", ":host()"].map Selectors.parse).all (·.isNone)
-- the pseudo-element a selector names, and its element
#guard ((Selectors.parse "#a::before").map fun l => l.map (·.pseudoElement)) == some [some "before"]
#guard ((Selectors.parse "div > p:first-child::marker").map fun l => l.map (·.pseudoElement)) == some [some "marker"]
-- forgiving selector lists of :is() and :where()
#guard ([":is(:unknown-pseudo(1, .b, .c))", ":is(.a, ::before, .b)", ":where()", ":is(:foo, div)"].map Selectors.parse).all (·.isSome)
#guard exIds ":is(:unknown-pseudo(1, .b, .c), #b)" == some ["b"]
-- comments are no tokens
#guard (["[foo='BAR'] /* sanity check (match) */", "[foo=bar/**/i]", "/**/a/**/>/**/b", "[foo='/*x*/']"].map Selectors.parse).all (·.isSome)
#guard (["a/**/b", "[foo='bar' /* x"].map Selectors.parse).all (·.isNone) || (Selectors.parse "a/**/b").isNone
-- pairs of pseudo-elements, and :has() in :has()
#guard (["::column::scroll-marker", "::before::column", "::before::marker", "::slotted(*)::checkmark",
  "::part(foo)::checkmark", "::part(foo)::before", "::before::column::scroll-marker"].map Selectors.parse).all (·.isSome)
#guard (["::column:hover", "::column::before", "::checkmark::checkmark", "::before::checkmark",
  "::marker::checkmark", "::slotted(*)::checkmark::slotted(*)", "::first-letter::column", "::column::slotted(*)",
  ".a:has(.b:has(.c))", ":has(:is(:has(a)))", ":has(> :not(:has(a)))"].map Selectors.parse).all (·.isNone)

/-! ## Form state and activation (DOM.Forms) -/

def formDoc : Dom := parseHtmlDocument
  "<body><form><input type=radio name=g id=r1 checked><input type=RADIO name=g id=r2><input type=checkbox id=c></form><label id=l><span id=s>x</span><input id=i></label><details><summary id=su>s</summary></details></body>"
def byId (d : Dom) (id : String) : NodeId := (d.getElementById 0 id).getD 0
-- checking a radio button unchecks the rest of its group; the attribute stays
#guard (let d := Forms.setChecked formDoc (byId formDoc "r2") true
  (Forms.checkedness d (byId d "r1"), Forms.checkedness d (byId d "r2"), (Forms.attr? d (byId d "r1") "checked").isSome)) == (false, true, true)
-- reset clears the dirty flag
#guard (let f := ((formDoc.treeOrder 0).find? (Forms.isHtml formDoc · ["form"])).getD 0
  let d := Forms.resetForm (Forms.setChecked formDoc (byId formDoc "r2") true) f
  Forms.checkedness d (byId d "r1")) == true
-- the activation target: the target itself, else the nearest ancestor when it bubbles
#guard Forms.activationTarget formDoc (byId formDoc "s") true == some (byId formDoc "l")
#guard Forms.activationTarget formDoc (byId formDoc "s") false == none
#guard Forms.activationTarget formDoc (byId formDoc "c") true == some (byId formDoc "c")
#guard Forms.isDetailsSummary formDoc (byId formDoc "su")
-- a label activates its first labelable descendant, not for a click on interactive content
#guard Forms.labelActivates formDoc (byId formDoc "l") (byId formDoc "s") == some (byId formDoc "i")
#guard Forms.labelActivates formDoc (byId formDoc "l") (byId formDoc "i") == none

-- Declarative shadow roots (HTML §13.2.6.4.4): the template leaves the tree, its children
-- go into the host's shadow root; DOMParser (shadow false) keeps the template.
def dsd : Dom := parseHtmlDocument "<div id='h'><template shadowrootmode='open'><p>s</p><slot></slot></template><b>x</b></div>"
#guard (match (dsd.get (byId dsd "h")).shadow with
  | some sr => (dsd.get sr).kids.size == 2 && dsd.isShadowRoot sr && (dsd.get (byId dsd "h")).kids.size == 1
  | none => false)
#guard (dsd.flatChildren (byId dsd "h")).map (fun k => (dsd.get k).lname) == #["p", "b"]
#guard ((dsd.get (byId dsd "h")).shadow.bind fun sr => (dsd.get sr).shadowInit.map (·.declarative)) == some true
#guard ((parseHtmlDocument "<div id='h'><template shadowrootmode='open'><p>s</p></template></div>" (shadow := false)).get
  (byId (parseHtmlDocument "<div id='h'><template shadowrootmode='open'><p>s</p></template></div>" (shadow := false)) "h")).shadow.isNone
-- an element that can not host a shadow root keeps its template
#guard (let d := parseHtmlDocument "<a id='h'><template shadowrootmode='closed'>s</template></a>"; (d.get (byId d "h")).shadow.isNone)
#guard dsd.wellFormed
-- a clonable shadow root is cloned with its host, deep or not
#guard (let d := parseHtmlDocument "<div id='h'><template shadowrootmode='open' shadowrootclonable>s</template></div>"
  let (d2, c) := d.cloneNode (byId d "h") false
  match (d2.get c).shadow with | some sr => (d2.get sr).kids.size == 1 | none => false)
#guard (let (d2, c) := dsd.cloneNode (byId dsd "h") true; (d2.get c).shadow.isNone)

-- Flattened slottables (DOM §4.2.2.3): the work-list version (`findFlattenedSlottables`)
-- answers what the recursive one (`flattenedGo`) does, for every slot, with slots nested
-- through two shadow trees, fallback children, and an unassigned slot.
def nestedSlots : Dom := parseHtmlDocument ("<div id='o'><template shadowrootmode='open'><div id='i'>" ++
  "<template shadowrootmode='open'><a>1</a><slot id='s3'><i>fb</i></slot><slot name='n'></slot></template>" ++
  "<slot id='s2'><u>fb2</u></slot><em slot='n'>e</em></div><slot name='z'><q>fb3</q></slot></template>" ++
  "<b>x</b><span>y</span>t</div>")
#guard (List.range nestedSlots.size).all fun k => !nestedSlots.isSlot k ||
  nestedSlots.findFlattenedSlottables k == nestedSlots.flattenedGo (nestedSlots.size + 1) k
#guard (List.range dsd.size).all fun k => !dsd.isSlot k || dsd.findFlattenedSlottables k == dsd.flattenedGo (dsd.size + 1) k
-- the inner default slot gets the outer slot, which flattens to the outer host's b, span and text
#guard (List.range nestedSlots.size).any fun k => nestedSlots.isSlot k && (nestedSlots.findFlattenedSlottables k).size == 3

-- the structural pseudo-classes counted in place agree with the sibling arrays
#guard (let d := parseHtmlDocument "<ul> <li>a</li> x <li>b</li><p>c</p> <li>d</li><p>e</p></ul><div><span>s</span></div>"
  (List.range d.size).all fun k =>
    (d.get k).type != .element || (d.get k).parent.isNone ||
    (let sibs := Selectors.elementSiblings d k
     let same := fun (c : NodeId) => (d.get c).lname == (d.get k).lname && (d.get c).ns == (d.get k).ns
     let st := sibs.filter same
     Selectors.edgeSib d k (fun _ => true) false == (sibs[0]? == some k) &&
     Selectors.edgeSib d k (fun _ => true) true == (sibs.back? == some k) &&
     Selectors.edgeSib d k same false == (st[0]? == some k) &&
     Selectors.edgeSib d k same true == (st.back? == some k) &&
     Selectors.sibPos d k (fun _ => true) false == (sibs.toList.findIdx? (· == k)).map (· + 1) &&
     Selectors.sibPos d k (fun _ => true) true == (sibs.toList.findIdx? (· == k)).map (sibs.size - ·) &&
     Selectors.sibPos d k same false == (st.toList.findIdx? (· == k)).map (· + 1)))


end L4Factoidal.DOM.Tests

