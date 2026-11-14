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

