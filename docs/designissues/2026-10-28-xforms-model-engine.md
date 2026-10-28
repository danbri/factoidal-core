# XForms: the model as a Lean engine over XDM, with no renderer

Date: 2026-10-28. Status: design, no code. Tracking:
https://github.com/danbri/factoidal/issues/1165 (section "Front end: design
first", XForms). Earlier plan, now partly done and partly replaced:
`docs/designissues/2026-07-05-xforms-model-program-plan.md` (F\*, XPath 1.0,
"bind and recalculate only").

## Result

The XForms processing model (instance, bind, model item properties,
rebuild, recalculate, revalidate, actions, submission) is a set of pure
functions from a model state and an input event to a new state and a list of
output requests. All of it runs in Lean and is testable with no renderer. The
browser draws controls from a view model that Lean computes, and sends user
input back as events. The browser makes no XForms decision (iron rule 7,
anti-pattern 36).

## 1. Target specifications (version-aware)

| Name in Lean | Specification | Expression language |
|---|---|---|
| `XForms11` | XForms 1.1, W3C Recommendation 2009-10-20 | XPath 1.0 |
| `XForms20` | XForms 2.0, W3C XForms Users Community Group draft (not a Recommendation; pin the dated draft and the repository commit at stage 1) | XPath 2.0 or later; this engine uses XPath 4.0 (`XPath4`) |

XForms 2.0 adds, among other items, attribute value templates, `var`,
custom functions and non-XML instances (JSON). It is a Community Group
draft and still changes. The engine is written for 2.0 over XDM and keeps a
1.1 mode with the XPath 1.0 evaluator, so a 1.1 test is judged by 1.1 rules.

## 2. What exists

- `formal/lean4/L4Factoidal/XForms/Bind.lean` (339 lines): the `type`,
  `relevant`, `required`, `readonly`, `constraint`, `calculate` properties, a
  dependency graph and Kahn's algorithm (a `calculate` cycle gives `none`),
  `recalculate`, `applyEdit`. `XForms/BindTests.lean`: `#guard`s.
- Limits of that module, which this design replaces: a bind's target is an
  element NAME (`findLeafIndex root name`), not a node-set from an XPath
  `nodeset`/`ref` expression; dependencies are names found by a syntactic scan
  of the `calculate` text (`calcNames`), not the nodes an evaluation reads;
  the `type` property knows 6 XSD types; evaluation is XPath 1.0
  (`XPath.Eval`) over `XML.Node`.
- Wasm op `xformsRecalc` and `npm/factoidal/test/xforms.test.js` (the only
  scored XForms test). `tools/lean-scoreboard.sh` row "XForms (Bind,
  recalculate)": no Lean runner (note n46).
- Available for reuse: XDM documents and XPath 4.0 (`XPath4/Doc.lean`,
  `XPath4/Eval.lean`), node replacement (`XPath4/Update.lean`, `fn:update`),
  XSD 1.1 simple types and facets (`XSD/SimpleType.lean`, `XSD/Facets.lean`,
  `XSD11/`), JSON to XDM (`XPath4/Json.lean`, for XForms 2.0 JSON
  instances), serialisation (`XPath4/Serialize.lean`), the HTTP request
  model used by the LWS client, the HTML parser for XForms in HTML hosts.

## 3. Test suites

- **W3C XForms 1.1 Test Suite**: https://www.w3.org/MarkUp/Forms/Test/XForms1.1/Edition1/
  (per chapter; each case is an XHTML+XForms document with a pass condition
  that a person reads on the screen). Vendor it to
  `third_party/testing/xforms11/` with `PROVENANCE.md` (URL, retrieval date,
  W3C test licence). Then classify every case into one of three groups:
  (a) **model**: the pass condition is a fact about instance data, a model
  item property or an event order. These are converted to machine checks: a
  sidecar JSON per case with the initial events, the user actions as events,
  and the expected instance and property values; (b) **UI**: the condition is
  about the drawing of a control; (c) **submission**: needs an HTTP peer,
  tested against a local server. The scoreboard reports the three groups
  apart, and the classification itself is a vendored file reviewed in a PR.
- **XForms 2.0**: the Community Group keeps a test suite next to the draft;
  stage 1 checks its location, form and licence, and vendors it if it has
  machine-checkable cases.
- **Own cases**: the existing `BindTests` and the npm test stay.

How far the existing work gets: today nothing of the W3C suite runs. The
existing `Bind` module covers part of chapter 6 (model item properties) for
binds whose target is one leaf element by name. A first estimate of the
"model" group, to be replaced by the stage 1 count: chapters 4 (processing
model), 6 (model item properties), 7 (XPath functions), 10 (actions) and
parts of 11 (submission) are model chapters; chapters 8 and 9 (controls,
container controls) are mostly UI.

## 4. The model and rendering split

| Part | Where | Note |
|---|---|---|
| Instance data (XML, and JSON for 2.0) | Lean | XDM trees; one instance set per model |
| Binds, model item properties, dependency graph | Lean | node identities, not names |
| Rebuild, recalculate, revalidate, refresh (the four default actions) | Lean | a state machine over events |
| XPath functions of XForms (`instance()`, `index()`, `current()`, `context()`, `if()`, ...) | Lean | added to the XPath 4 function table under the XForms namespace |
| Actions (`setvalue`, `insert`, `delete`, `toggle`, `send`, `dispatch`, `reset`, ...) | Lean | event handlers produce new state |
| Submission (serialise, validate, request, replace) | Lean decides; host does the I/O | the request is a value; the response comes back as an event; a network read gets a retrieval record (owner rule of 2026-10-25) |
| UI binding (which control shows which node, its value, label, relevant/readonly/required/valid states, `repeat` items) | Lean | a "view model" value per refresh |
| Drawing the controls, focus, keyboard | Browser | JS maps the view model to HTML elements and sends `xforms-value-changed`-class events back; it has no XForms logic |

The view model is the boundary. A renderer in the hub (Observable cell), a
renderer in a terminal and a test driver all read the same value. The test
driver needs no browser.

## 5. Engine shape

```
structure Model where          -- per <model>
  instances : List (String × XDMDoc)
  binds     : List BindDecl    -- nodeset/ref expressions, MIP expressions
  graph     : DepGraph         -- built by rebuild: vertices are (node, property)
  mips      : NodeMap Mips     -- computed properties per node
  pending   : Flags            -- rebuild/recalculate/revalidate/refresh needed

def step : Model → Event → Model × List Output   -- Output: view model, submission request, message, error
```

- Dependencies: the dependency graph vertices are (node, property) pairs. The
  edges come from the nodes that an evaluation of each expression reads, so
  the evaluator gets a "read set" mode. This replaces the name scan.
- Recalculation order: topological order of the subgraph reachable from the
  changed nodes. Cycle: an `xforms-compute-exception`, as the specification
  says.
- Loops: event processing is a loop over a queue (`repeat`/fuel by queue
  length), not one frame per event (tail recursion rule).

## 6. Theorems to aim for

1. **Order independence**: every topological order of the dependency
   subgraph gives the same instance after recalculation.
2. **Fixed point**: recalculating twice with no change in between gives the
   same model (idempotence).
3. **Incremental equals full**: the result of recalculating only the
   vertices reachable from the changed nodes equals a full recalculation.
4. **Cycle soundness**: `rebuild` reports a cycle if and only if the
   `calculate` dependency graph has one.
5. **Version link**: for a 1.1 form whose expressions are in the XPath 1.0
   subset that XPath 2.0 backwards compatible mode keeps, the `XForms11`
   (XPath 1.0) and `XForms20` (XPath 4.0) engines compute the same string,
   boolean and number values. Stated over the expression fragment, with
   the specification versions named in the statement.
6. **Refines the existing module**: for binds whose target is one leaf by
   name and whose `calculate` refers to leaves by name, the new engine gives
   the output of `XForms.Bind.recalculate`. Then the old module is removed
   (no second implementation).
7. **Type property**: the `type` check equals `XSD` validation of the
   lexical form against the simple type (any built-in or user-derived type),
   reusing the XSD theorems.

## 7. Staged plan

| Stage | Work | Measure |
|---|---|---|
| 1 | Vendor the XForms 1.1 suite with provenance; classify cases (model, UI, submission); locate the XForms 2.0 suite | counts per group, in the ledger |
| 2 | `l4xforms` runner over the model group with the existing `Bind` module, so a baseline exists | pass, fail (out of N model cases) |
| 3 | `XForms/Model.lean`: binds by node-set over XPath 4 XDM, read-set dependencies, the four default actions; theorems 1, 4, 6 | runner score; theorem build |
| 4 | Actions (chapter 10) and XForms XPath functions; theorems 2, 3 | runner score |
| 5 | View model and a hub renderer (Observable cell over the wasm op) | browser sweep in `tests/web-demos` |
| 6 | Submission: request value, host I/O with retrieval record, response events; the feature-combination invariants of https://github.com/danbri/factoidal/issues/1120 (a form can make a request to any URL: same rules as the LWS client) | submission group score against a local server |
| 7 | XForms 2.0 mode (AVTs, `var`, JSON instances); theorem 5 | 2.0 suite score if one exists |

## 8. Decisions recorded here (coordinator, not owner)

- XForms 2.0 over XPath 4.0 is the main engine; 1.1 is a mode, not a second
  engine.
- The browser renders a Lean view model and sends events; it holds no model
  state of its own.
- The W3C 1.1 suite is converted by classification plus sidecar expectations,
  because its pass conditions are written for a person.
