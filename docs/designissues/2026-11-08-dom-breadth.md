# DOM breadth for page scripts: markup, ranges, selection, traversal, reflection, computed style

Date: 2026-11-08. Author: dombreadth, a subagent of session depmap-0e.
Records it joins: `2026-11-08-page-scripts.md` (the page objects and the imports) and
`2026-11-08-lean-js-engine.md` (BubblePopJS).

## 1. What pages get

- Markup: the `innerHTML` setter, `outerHTML` (get and set), `insertAdjacentHTML`,
  `setHTMLUnsafe`, `getHTML`, `Document.parseHTMLUnsafe`, `Range.createContextualFragment`.
  The getters now use Lean's HTML fragment serialization algorithm; the JavaScript
  serializer of the prelude is gone.
- `Range` and `StaticRange` (DOM §5): every method of `Range`, live: each change of the
  tree moves the live ranges as the DOM Standard says.
- `Selection` (Selection API): `getSelection()` on the window and the document, and all
  the methods but `modify`.
- `NodeIterator` and `TreeWalker` (DOM §6), with filters, and `NodeFilter`.
- The reflected IDL attributes of HTML elements (HTML §2.6.1), from one Lean table.
- `getComputedStyle` with the resolved values of the properties Lean's cascade computes, as
  a read-only CSSStyleDeclaration (`'color' in style`, dashed and camel-cased names,
  `length`, `item`, iteration).
- The `CSS` namespace: `CSS.supports` (both forms) and `CSS.escape`.
- `document.fonts`: a FontFaceSet that is loaded (the fonts of a page are held before its
  scripts run, and a page can not add font faces yet), `ready` resolved.

## 2. Where the algorithms are

All in Lean; prelude.js converts arguments, makes the objects and calls the page's filter
callbacks.

- `L4Factoidal/DOM/Fragment.lean`: the HTML fragment parsing algorithm into a
  DocumentFragment (the parser is `HTML.TreeBuilder.parseFragmentState`), and the HTML
  fragment serialization algorithm.
- `L4Factoidal/DOM/Range.lean`: boundary points and their position, set the start or end,
  compare, contains, the stringifier, and the step functions of the mutation algorithms
  that move a boundary point. Theorems: the position of a point to itself is equal, and on
  one node the position is antisymmetric; each step keeps an offset within its node's new
  length (`insertStep_le`, `removeStep_parent_le`, `replaceDataStep_le`).
- `L4Factoidal/DOM/Live.lean`: the live ranges and NodeIterators of a page, moved by the
  mutation algorithms (insert, remove, replace, replace all, adopt, replace data, split a
  Text node, normalize), each step in the standard's order.
- `L4Factoidal/DOM/Traversal.lean`: the NodeIterator pre-removing steps and traverse, and
  the TreeWalker methods as machines that stop where the standard says "filter": the
  machine answers a node for the page's filter, the page answers the filter result, the
  machine goes on.
- `L4Factoidal/DOM/Reflect.lean`: the table of reflected attributes (written by hand from
  the HTML standard's element sections, checked against WPT `html/dom/elements-*.js`), the
  rules for parsing integers, non-negative integers and floating-point numbers, and the
  getter and setter of each reflected type.
- `L4Factoidal/WasmVM/Hosts/DomOps.lean`: the operations, as `node_query` ops from 100.
  Each change of the tree is a typed command (two new ones: `replaceData`, `splitText`),
  recorded as all others, so a replay of the commands gives the same arena.
- `L4Factoidal/Rendering/ComputedValues.lean`: the CSS text of each computed value.
- `L4Factoidal/Rendering/CssSupports.lean`: the `<supports-condition>` grammar over
  `CSS.supportsDeclaration` (appended to `Style.lean`: a declaration this profile reads and
  applies) and `DOM.Selectors`, and "serialize an identifier" for `CSS.escape`.

## 3. No new native

The ops use `n.query(id, op, s)`, the native both engines already have:
`Hosts.Page.serveExtra` sends ops from 100 to `Hosts.Dom.domOp` with the page's DOM state.
An op that changes the tree answers a short string, so the QuickJS guest's first buffer
holds it and the import runs once. Ops 20 and 21 are layout reads (`WebDocument.measure`):
20 the computed style (the cascade alone, no layout), 21 the used width and height.

## 4. Cost

- A page with no live range and no NodeIterator runs no live step: `addCommand` checks
  `Live.idle` once per command.
- A collected `Range` object releases its live range (QuickJS-NG: `FinalizationRegistry`),
  so the live ranges are those the page can reach. BubblePopJS has no GC yet, so there a
  page's ranges stay until it ends.
- A removal builds the set of the removed subtree once; each range then costs one lookup.
- Reflection: the rows of every interface are installed when the prelude runs, which the
  engine does once and copies for each page; a get is one host call; a set is one host call
  (Lean sets the content attribute) unless a MutationObserver is registered or the row is
  a URL (then the decision, then `setAttribute`).
- `getComputedStyle`: a style property reads the cascade of the current DOM version (made
  once per version); only `width` and `height` read the layout.

## 5. Not done

- `document.write` and `writeln`: they need the parser's insertion point.
- `matchMedia` on Lean's media queries: the MediaQuery module is not on main yet.
- The page's selection is not yet the user's drag selection (WebSelection is geometric,
  over glyph cells), and Lean does not paint it yet.
- XML documents: their markup is parsed and serialized as HTML.
- Mutation records for the changes of the Range algorithms.
