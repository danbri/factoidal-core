# XForms 1.1: the model engine, measured on the W3C test suite

Date: 2026-11-14. Status: first stage built and measured; not complete.
Design: `docs/designissues/2026-10-28-xforms-model-engine.md`. This record
says what exists, what the W3C XForms 1.1 Test Suite shows, and what is
proved, tested only, or open.

## What is implemented

New modules under `formal/lean4/L4Factoidal/XForms/` (the older `Bind.lean`,
its Wasm op `xformsRecalc` and its npm test are unchanged and not touched):

| Module | Content |
|---|---|
| `DepGraph.lean` | Dependency graph of recalculation over any vertex type: Kahn's algorithm (`topoSort`, tail recursive), topological order, cyclic core, recalculation over an arbitrary evaluation function |
| `Theorems.lean` | The theorems listed below; imported by the runner so they are built with it |
| `Eval.lean` | XPath 1.0 expression walk with fuel, recording the nodes each location step selects (the read set), plus the XForms function library of §7.6 to §7.11 |
| `Model.lean` | `step : Model → Event → Model × List Output`: the form as an element table, instance data, binds and model item properties, rebuild / recalculate / refresh, the view model, events and actions |
| `Harness/XFormsRun.lean` | `lake exe l4xforms`: the suite runner (a plain `lean_exe`, outside the library root, so the Wasm build and the npm package do not change) |

Choices:

- **Expression language.** XForms 1.1 expressions are XPath 1.0 and are
  judged by XPath 1.0 rules: the engine uses the XPath 1.0 data model and
  definitions of `L4Factoidal.XPath` (`XPath.Full`: node tests, axes,
  comparisons, number to string conversion, the core function library).
  XPath 4.0 in compatibility mode is not used, so no argument about the
  differences is needed. Only the expression walk is new (`Eval.evalE`),
  because the existing walk has a fixed function table and no read set; the
  core functions are reached by calling the existing evaluator with the
  argument values bound to variables.
- **Instance data** is the XPath 1.0 data model over the project's XML tree,
  a node being addressed by document number and child-index path. The XDM
  table of `XPath4/Doc.lean` is the data model for the later XForms 2.0 mode
  (stage 7 of the design), not used here.
- **Dependencies** are read sets from evaluation, per calculated node
  (address), not names scanned from the expression text. A node's reference
  to itself is not a dependency (§4.3.2).
- **Event processing** is a work list processed by a loop with fuel
  (`Model.run`, tail recursive). `dispatch` puts the handlers of the event in
  front of the rest of the running action, so delivery is synchronous without
  a stack frame per event. The outermost handler ends with the deferred update.
- **No I/O in the engine.** Linked resources (`instance/@src`, `@resource`,
  `model/@schema`, `label/@src`) are supplied by the host as a list of
  (URI, content); a missing one is `xforms-link-exception`. The clock and the
  timezone are host inputs (`now()`, `local-date()`).
- **Hashes.** `digest()` and `hmac()` call `Crypto.md5`, `Crypto.sha1`,
  `Crypto.sha256`, `Crypto.sha384`, `Crypto.sha512` and `Crypto.hmacWith`
  already in the tree; the engine defines no cryptographic step (only the
  base64 and hex text encodings of the result).

Covered by `Model.lean`: `instance` (inline, `src`, `resource`); nested `bind`
with `nodeset` and `type`, `readonly`, `required`, `relevant`, `calculate`,
`constraint` (inheritance of `relevant` and `readonly`); the XML Schema
built-in types through `XSD.validLexicalFor` and the XForms datatypes
`listItem`, `listItems`, `dayTimeDuration`, `yearMonthDuration`, `email`,
`card-number`; `xforms-model-construct`, `-construct-done`, `xforms-ready`,
`xforms-rebuild`, `-recalculate`, `-revalidate`, `-refresh`, `-reset`, the
notification events on refresh (`xforms-value-changed`, `-valid`, `-invalid`,
`-readonly`, `-readwrite`, `-required`, `-optional`, `-enabled`, `-disabled`),
`xforms-focus` with `DOMFocusIn` / `DOMFocusOut`, `xforms-help` / `-hint`,
`xforms-select` / `-deselect` for `case`, `xforms-scroll-first` / `-last`,
`xforms-insert` / `-delete`, the exception events as fatal errors; the
actions `action`, `setvalue`, `insert`, `delete` (element nodes), `setindex`,
`toggle`, `setfocus`, `dispatch` (with `delay` as later delivery), `rebuild`,
`recalculate`, `revalidate`, `refresh`, `reset`, `load`, `message`, with `if`
and `while`; the view model for `input`, `secret`, `textarea`, `output`,
`upload`, `range`, `trigger`, `submit`, `select`, `select1` inside `group`,
`switch` / `case` and `repeat`.

Not implemented (reported by the engine as unsupported, never as a result, or
simply absent): submission (§11) and `send`; `p3ptype`; schema-defined types;
`itemset` / `copy` and the item lists of `select` / `select1`; `alert`;
`xforms-in-range` / `-out-of-range`; `xforms-output-error`; `insert` /
`delete` of attributes; the effect of `insert` / `delete` on repeat indexes
(§9.3.6); `iterate` (not an XForms 1.1 attribute); `power()` with a
non-integer exponent; the XForms `id()` function with two arguments.

## The suite and its classification

The suite is vendored unchanged at `third_party/testing/xforms11/` (see its
`PROVENANCE.md`). `tests/xforms11/classification.json` classifies 461 entries
(the 460 test documents and `h.3`, which the driver page lists and which has
no XHTML document), each with a one-line reason:

- (a) model: the condition is a fact about instance data, a computed value, a
  model item property, an event or its order, an error event, a message;
- (b) view model: the condition is about what a control shows or whether it is
  available, decided from the view model with no person;
- (c) submission: needs an HTTP peer (decidable against a scripted peer);
- (d) needs a human reader.

The driver pages list 500 entries; 43 of them (the chapter 1 list) repeat
cases of other chapters and are counted once. Four test documents are not
named by any driver page (`g.3`, `9.2.3.a`, `9.2.3.1.a`, `9.2.3.1.b`).

`tests/xforms11/expect/<case>.json` holds, for a case that is scripted, the
sentence of the test that states its pass condition (`quote`, taken from the
test document's own text) and the steps and checks derived from it. A case
with no sidecar is counted unsupported.

## Cases that need a human reader (29, never scored)

| Chapter | Count | Cases | Why no machine check |
|---|---|---|---|
| 4 | 3 | 4.3.6.b | keyboard navigation order (`navindex`, non-normative), tried by a person at a keyboard |
| | | 4.8.1.a, 4.8.1.b | need a host script engine calling `getInstanceDocument()`; the condition is optional ("may have seen") |
| 8 | 9 | 8.1.a | keyboard navigation order and access keys |
| | | 8.1.2.b, 8.1.3.b, 8.1.4.b | the condition accepts any of several renderer behaviours ("must not work correctly, generate an error, not appear on this page or otherwise make the problem known") |
| | | 8.1.5.d, 8.1.5.1.a | the condition is that an image is drawn |
| | | 8.1.6.a | about the host's file chooser, and optional ("may be limited") |
| | | 8.1.7.f, 8.1.7.g | "all of the range elements must work" does not say what to observe |
| 10 | 4 | 10.8.c, 10.8.3.a, 10.8.3.b, 10.8.3.c | the condition compares how fast two messages appear, a judgement of elapsed time (the engine does deliver a delayed event later, but the stated condition is about time as a person sees it) |
| Appendix G | 10 | G.1.a to G.1.e, G.2.a to G.2.d, g.3 | the condition is how CSS styles (colours, borders, fonts) are drawn |
| Appendix H | 3 | H.1, H.2, H.3 | complete example forms with no stated pass condition |

## Theorems (`XForms/Theorems.lean`)

All are at the level of the dependency graph: any vertex type with decidable
equality, any `deps`, any evaluation function `ev` that reads only its
declared dependencies (`Local deps ev`). `#print axioms` shows only
`propext`, `Quot.sound` and, for `topoSort_none_iff_cycle`, `Classical.choice`.

| Theorem | Says |
|---|---|
| `topoSort_topological` | the order the engine recalculates in (the answer of `topoSort`) is a topological order of the dependency graph and holds exactly the given vertices |
| `topoSort_none_iff_cycle` | `topoSort` fails (the engine raises `xforms-compute-exception`) if and only if the graph has a cyclic core: a non-empty set of vertices each reading a member of the set |
| `topo_no_cycle` | a topological order holds no cyclic core |
| `recalc_solves` | after recalculation in a topological order every computed vertex holds the value of its expression in the final state, and nothing else changed |
| `solution_unique` | two states that agree outside a topological order and both solve the equations on it are equal |
| `recalc_fixed_point` | recalculating again changes nothing |
| `recalc_order_independent` | any two topological orders of the same vertices give the same state |
| `topo_filter` | a sub-list of a topological order is a topological order |
| `recalc_incremental` | recalculating only a set of marked vertices that is closed under "reads something changed or marked" equals recalculating all |

Proved: the nine statements above.

Tested only (`#guard`s and the suite run): that the engine's read sets are
the true dependencies of its expressions (the hypothesis `Local` for the
engine's graph: the XPath core library is reached through
`XPath.Full.evalExpr`, a `partial def` the kernel cannot unfold); the XForms
functions (date arithmetic, durations, the Luhn check, base64); every part of
`Model.lean`.

Open:

- The link from the abstract `recalc` to `Model.recalc` (a state of instance
  documents, not a function from vertices to values) is not stated.
- The equivalence of "cyclic core" and "directed cycle" for a finite graph is
  stated in a comment, not proved.
- The engine recalculates every vertex; `recalc_incremental` is proved but the
  incremental form is not used.
- Refinement of `XForms.Bind.recalculate`: not proved, and not true as an
  equality on all inputs. The old module takes dependencies from the names
  that occur in the `calculate` text; the new one from the nodes an evaluation
  reads. They differ when a name occurs in a branch that is not evaluated (the
  old module then reports a cycle or orders by a dependency the new one does
  not have). On binds whose target is one leaf by name and whose `calculate`
  reads every leaf it names, both evaluate the same expression with the same
  context node through the same `XPath.Full` definitions; a proof would have
  to go through `evalExpr`, which is opaque. No differential test of the two
  modules has been written yet.
- Order independence and the fixed point for the full engine with `insert` /
  `delete` (which change the vertex set) are not stated.
- Theorems 5 and 7 of the design (version link to XForms 2.0, the `type`
  property against XSD validation) are not started.

## Measured counts

Run of `lake exe l4xforms` on commit a8c79c26e (built from that tree,
2026-11-14 05:32 UTC), 186 sidecars. The whole run takes under 0.1 s (93 ms);
`lake build l4xforms` on top of the already built XML and XPath modules takes
under one minute. "Unsupported" is a case with no sidecar yet, or a run in
which the engine reported something it does not implement; it is never a pass.

| Chapter | (a) model | (b) view model | (c) submission | (d) human reader |
|---|---|---|---|---|
| 2 | | | 0 pass, 0 fail, 4 unsupported (out of 4) | |
| 3 | 18 pass, 2 fail, 13 unsupported (out of 33) | 0 pass, 0 fail, 2 unsupported (out of 2) | 0 pass, 0 fail, 2 unsupported (out of 2) | |
| 4 | 33 pass, 4 fail, 21 unsupported (out of 58) | | 0 pass, 0 fail, 6 unsupported (out of 6) | 3 |
| 5 | 5 pass, 0 fail, 10 unsupported (out of 15) | | | |
| 6 | 8 pass, 0 fail, 1 unsupported (out of 9) | | 0 pass, 0 fail, 2 unsupported (out of 2) | |
| 7 | 48 pass, 2 fail, 12 unsupported (out of 62) | | | |
| 8 | | 13 pass, 3 fail, 33 unsupported (out of 49) | 0 pass, 0 fail, 1 unsupported (out of 1) | 9 |
| 9 | | 9 pass, 1 fail, 14 unsupported (out of 24) | | |
| 10 | 29 pass, 1 fail, 27 unsupported (out of 57) | 2 pass, 0 fail, 6 unsupported (out of 8) | 0 pass, 0 fail, 1 unsupported (out of 1) | 4 |
| 11 | | | 0 pass, 0 fail, 84 unsupported (out of 84) | |
| Appendix B | 7 pass, 0 fail, 8 unsupported (out of 15) | | | |
| Appendix G | | | | 10 |
| Appendix H | | | | 3 |
| **Total** | **148 pass, 9 fail, 92 unsupported (out of 249)** | **24 pass, 4 fail, 55 unsupported (out of 83)** | **0 pass, 0 fail, 100 unsupported (out of 100)** | **29** |

Before: the first run (de30df48f, 178 sidecars) gave model 128 pass, 23 fail,
98 unsupported; view model 22 pass, 5 fail, 56 unsupported.

The failures of this run, by cause:

- not implemented: `itemset` bindings (3.2.4.e, 3.2.4.f), lazy authoring
  (4.2.2.c2), `range` events and the datatypes `range` accepts (4.4.16.a,
  4.4.17.a, 8.1.1.a), `xforms-output-error` (4.5.5.a), `alert` (8.1.5.c),
  `select1` items (8.3.3.b);
- 7.10.3.b: the XForms `id()` function with a node-set second argument;
- 10.2.a: under examination (a control of the test is not found by its label);
- 7.9.8.a calls `adjust-dateTime-to-timezone()` with no argument and expects
  an empty output; the engine treats the wrong number of arguments as an
  error;
- 9.2.3.1.a (a document no driver page lists) has `<case value="out"/>`
  inside `toggle`; `value` is an expression (§10.6.1), `out` selects no node,
  so no case is toggled.

6.2.1.a uses a type defined by an inline schema; the engine reports it as
unsupported.

## Final measured run (as merged to main, 4c41cd013)

`l4xforms` built from the merged tree: (a) model 212 pass, 6 fail, 31 unsupported (out of 249); (b) view model 42 pass,
5 fail, 36 unsupported (out of 83); (c) submission 0 pass, 0 fail, 100 unsupported (out of 100); (d) 29 need a human
reader (not scored). The last changes: the text of a control's `alert` and its in-range state (`xforms-in-range` /
`xforms-out-of-range` on `range`), focus given to a group moves to its first form control (`Form.firstControlGo`, a
fuel-bounded work list). The modules are imported by the library root, so the full Lean build checks the
recalculation theorems.
