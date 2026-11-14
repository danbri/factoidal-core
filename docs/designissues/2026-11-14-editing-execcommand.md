# Editing: `execCommand` and the editing algorithms (2026-11-14)

`editing/` was the largest single loss outside CSS in the full run of main `6dde36491`:
6,159 of Chrome's 117,099 subtests. `document.execCommand` and the `queryCommand*` methods
did not exist, so 74,111 subtests failed with "an exception must not be thrown". Rich-text
editors on real sites call these methods on `contenteditable` content.

## What is implemented

The W3C Editing APIs draft ("execCommand"), in `formal/lean4/L4Factoidal/DOM/Editing/`:

| Module | Content |
|---|---|
| `Style.lean` | The inline style as a list of declarations; colours; font sizes; the resolved values editing reads (`display`, `font-weight`, `font-style`, `text-decoration`, `color`, `background-color`, `font-family`, `font-size`, `text-align`, `white-space`) from HTML defaults, the page's sheets and the `style` attribute. |
| `Core.lean` | The editing state (`Ed`), the primitive changes (`Prim`) and their guard, editable nodes and editing hosts, block and inline nodes, visibility, line breaks, allowed children, move preserving ranges, set the tag name, wrap, split the parent, block boundary points, block-extend. |
| `Inline.lean` | Effectively contained nodes, modifiable elements, effective and specified command values, record and restore values, clear / push down / force the value, set the selection's value, state and value overrides, the inline commands. |
| `Block.lean` | Fix disallowed ancestors, normalize sublists, the selection's list state, alignment value, indent, outdent, toggle lists, justify the selection, `formatBlock`. |
| `Delete.lean` | Canonical space sequences, canonicalize whitespace, equivalent points, delete the selection, the Range insert and extract algorithms, automatic linking, `delete`, `forwardDelete`, `insertHorizontalRule`, `insertHTML`, `insertImage`, `insertLineBreak`, `insertParagraph`, `insertText`. |
| `Commands.lean` | `execCommand`, `queryCommandEnabled`, `-Indeterm`, `-State`, `-Supported`, `-Value`; the `input` event of a command. |
| `Tests.lean` | 37 WPT cases as `#guard`, and property checks on nine inputs. |

Commands: `backColor`, `bold`, `createLink`, `defaultParagraphSeparator`, `delete`,
`fontName`, `fontSize`, `foreColor`, `formatBlock`, `forwardDelete`, `hiliteColor`,
`indent`, `insertHorizontalRule`, `insertHTML`, `insertImage`, `insertLineBreak`,
`insertOrderedList`, `insertParagraph`, `insertText`, `insertUnorderedList`, `italic`,
`justifyCenter`, `justifyFull`, `justifyLeft`, `justifyRight`, `outdent`, `removeFormat`,
`selectAll`, `strikethrough`, `styleWithCSS`, `subscript`, `superscript`, `underline`,
`unlink`, `useCSS`. Not supported (answer false): `copy`, `cut`, `paste`, `undo`, `redo`.

Page API (prelude.js, WebIDL glue only): `document.execCommand`, `queryCommandEnabled`,
`queryCommandIndeterm`, `queryCommandState`, `queryCommandSupported`, `queryCommandValue`,
`document.designMode`, `element.contentEditable`, `element.isContentEditable`; `focus()` of
an editing host moves the selection into it; a command fires a trusted `input` event
(`InputEvent` with `inputType` and `data`) at the affected editing host.

## How it runs

- The algorithms are pure functions of an editing state: the DOM arena (`DOM.Arena`), the
  live ranges (`DOM.Live`; slot 0 is the active range), the document's editing flags and a
  log of primitive changes. Nothing else is read.
- Every change of the arena goes through `applyPrim`. It does nothing unless each node the
  change touches is in no document or is inside an editing host (`permitted`), so a command
  can not change content outside the editing host.
- The host (`Hosts.Dom.editOp`, `node_query` ops 175 to 177) runs the command on the page's
  arena, then replays the logged changes as its typed DOM commands, so the layout replay,
  the page's other live ranges and NodeIterators see the same changes. The selection's range
  becomes the active range the command left. The flags are kept in `State.edit`.
- Styles: `Hosts.Page` asks the layout reads for the text of the page's sheets (measure op
  40, no layout), `editOp` parses it once per command (`Rendering.CSS.parseIn`) and gives
  the editing module the declarations each element gets from it (`editSheet`).

## Measured

Engine built in the cloud from the branch (`branch-wpt.yml`), names `/editing/` and
`sample:150`, WPT `2358bd4835`, baseline the full run of main `6dde36491`.

| Step | editing/run (of 96,745) | editing/other (of 16,742) | plaintext-only (of 1,707) | whitespaces (of 1,655) | All names of the run |
|---|---|---|---|---|---|
| Baseline | 6,063 | 78 | 1 | 2 | 13,918 |
| `e1f37e4d3` (inline commands, queries) | 68,129 | 1,017 | 542 | 21 | 77,581 |

Worse in that run: three tests, four subtests, all by TIMEOUT (two editing tests that get
further than before and then wait for key events; one `content-security-policy` test this
change does not touch).

The pure module is also run by the Lean interpreter over all 35 WPT data files
(`editing/data/*.js`, 6,976 cases; return values, innerHTML and the six queries of each
queried command): 88,440 of 89,644 subtests (98.7%).

## Where the code follows the WPT expectations, not the draft

The expectations in `editing/data` were updated to what browsers do. Where they differ from
the draft's text the code follows them, with a comment at each place:

- `strikethrough` makes `<strike>`, not `<s>`.
- "Delete the selection" removes the inline wrappers a removal emptied before it adds the
  `br` that keeps the block open (`<p><br></p>`, not `<p><b><br></b></p>`).
- `insertParagraph` gives an empty line copies of the inline formatting elements around the
  caret (not of links, nor of what is inside one).
- `formatBlock` takes the sectioning blocks (`article`, `blockquote`, `section`, ...).
- A colour command with a value that is not a colour answers true and changes nothing.
- No `beforeinput` for `execCommand`; `input` carries `inputType` and `data`.

"Collapsed line break" and "extraneous line break" are defined by layout in the draft. Here
they are decided on the tree (`contentAfter`, `contentBefore` in `Core.lean`).

## Proved, tested, open

Proved (Lean theorems, no `sorry`, axioms only `propext`, `Classical.choice`, `Quot.sound`):

- `applyPrim_refused`: a change that is not permitted leaves the editing state as it was.
  `applyPrim_log`: each change logs at most itself.
- `exec_unsupported`: `execCommand` of a command that is not supported answers false and
  changes nothing. `enabled_needs_range`: without an active range only the miscellaneous
  commands are enabled.
- `getState_setState`, `setState_toggle`: a toggle with nothing to format is read back by
  the next state query, and a second toggle undoes it (the state override).
- `equivalentValues_refl`; `recordValues_size` (nine entries a node).
- Inline style: `getDecl_setDecl`, `getDecl_removeDecl`, `setDecl_idem`.
- `parseHex_toHex` (an opaque colour survives its hexadecimal form),
  `cssSizeToLegacy_legacySizeToCss`, `legacyOfPx_mono`.
- `canonicalSpaceSequence_length` (n characters for n spaces) and `_chars` (only U+0020
  and U+00A0). `alignmentValue_mem`.

Tested only:

- The tree algorithms, on the 6,976 WPT cases and the `#guard` cases.
- On every WPT input: nothing outside the editable `div` changes (0 failures); the
  selection is inside the editing host after the commands (1 failure in 6,976: `selectAll`, which selects the body); "restore
  the values" after "record the values" changes nothing (0); "delete the selection" leaves
  a collapsed range in the host (0); the block-extended range contains the range (0).

Open:

- Block-extend is not idempotent: `<p>foo<br>[bar]<br>baz</p>` is a counterexample (the
  end stops after a `br`, a block start point that is not a block end point). The property
  to prove is containment, which is tested, not proved.
- No theorem yet that a permitted change leaves every node outside the host as it was: the
  guard is per change, and `permitted` asks that the old parent of a moved node is inside
  the host too.
- The host's replay of the log is checked at run time (the arena sizes must agree, and each
  made node must get the number the pure run gave it); it is not proved equal.
- Performance: a style read walks the element's ancestors and matches the sheet's rules at
  each one, with no cache; a command on a large page with large sheets will be slow. A page
  that does not call these methods pays nothing (no code runs outside ops 175 to 177).
- Not done: `copy`, `cut`, `paste`, `undo`, `redo`; commands in `input` and `textarea`;
  key events to editing commands (most of `editing/other`, `input-events`);
  `beforeinput` and `getTargetRanges()`; `contenteditable=plaintext-only` rules.
