# XQuery Update Facility in Lean (2026-10-28)

Tracking: https://github.com/danbri/factoidal/issues/1101 (QT4). Code:
`formal/lean4/L4Factoidal/XQueryUpdate/`. Tests: qt4tests `upd/` (40 test
sets, 825 test cases, commit b39c4bc0), vendored in
`third_party/testing/qt4tests/upd/`.

Specification: XQuery Update Facility 3.0, W3C Recommendation 2017-01-24
(https://www.w3.org/TR/xquery-update-30/). The QT4 Community Group has no
4.0 draft of it. The tree adds it to XQuery 4.0 (`L4Factoidal/XQuery4/`).

## How it works

**Pending update lists.** An updating expression returns an XDM instance
and a pending update list (§2.1). Here an update primitive (§8.1) is an
item in the result sequence: a function item `#upd:<kind>` partially
applied to its operands (`Pul.Prim.toItem`). No query can write the
namespace `#upd`. So the comma operator, FLWOR, `if`, `typeswitch` and
function calls merge pending update lists by sequence concatenation, which
is `upd:mergeUpdates` (§8.2.2), and the shared type `XPath4.Item` does not
change. `splitPul` takes the XDM instance and the list apart.

**applyUpdates** (`Pul.applyUpdates`, §8.2.3). The compatibility check
(XUDY0015, 0016, 0017, 0024, 0031) runs first. Then every document that a
primitive targets is rebuilt from the snapshot: the operation tables of
`collectOps` are applied in one bottom-up pass (`rebuild`), with the rule
order of §8.2.3 where it matters (replaceElementContent wins over the
insertions, a replaced node takes its replacement, insertions next to a
deleted node stay). Adjacent text nodes are merged and empty text nodes
are removed (`mergeKids`). A deleted or replaced subtree is still checked
for the XDM constraints (XUDY0021). The new table is flattened by `flatU`,
which is `XPath4.flatXT` with the copy-namespaces inherit mode as a
parameter.

**Types.** `upd:removeType` (§8.2.5) applies to the nodes that §8.1 names
for each primitive and to their ancestors. Inserted content under an
untyped parent, and content inserted with `declare construction strip`, is
untyped (`upd:setToUntyped`). A copy (copy modify, §5.6) is untyped.

**Revalidation** (`Revalidate.lean`, §8.2.4). With `strict` or `lax`, a
changed document or copy is validated again through the XSD 1.1 schema
hook (`SchemaHook.validateIn`). The default revalidation mode is
implementation-defined (§3.1, "Overwritable"); here it is `skip`, so a
module without `declare revalidation` does not validate. The supported
modes are a setting (`revalSupportedKey`); a mode that is not supported is
XUST0026.

**Expressions** (`Expr.lean`, `Grammar.lean`). insert, delete, replace,
replace value of, rename, copy modify, `transform with` (read by
`XPath4.Parser.pCast` when a grammar extension is present), `invoke
updating`, `%updating` and `%simple` inline functions, `declare updating
function`, `fn:put` (with `fn:put#2` and `#3`). A dynamic call of an
updating function without `invoke updating` is XUDY0038.

**Top level** (`Query.evalUpdQuery`, §2.5). The category rules run before
evaluation; when the query body returns a pending update list,
`applyUpdates` and revalidation run, and each `fn:put` stores a document
under its URI in the returned dynamic context.

## Decision: the category rules of the tests

The `upd/` test sets were converted in 2021 from the XQUTS 1.0 suite.
Their expected errors follow the XQuery Update Facility 1.0 category rules
(https://www.w3.org/TR/xquery-update-10/ §2.2, §2.4, §2.5): XUST0002 (an
updating function body or a modify clause that is simple, not vacuous) and
XUST0028 (an updating function with a return type) exist only in 1.0, and
about 100 tests expect XUST0001 for a comma or `if` that mixes updating and
simple expressions, which 3.0 §7.4 and §7.6 allow. One test,
`id-transform-expr-014`, was changed upstream on 2026-09-26 to the 3.0 rule
for the return clause of copy modify ("updating return clause is allowed").

So `Static.cat` has two rule sets. The runner uses the 1.0 rules with the
3.0 return clause (`v10 := true`), which is what the test sets expect. The
3.0 rules are the setting `v10 := false`. Who decided: the update agent,
from the expected results of the tests.

## Changes in shared code

All small, each with a reason:

- `XQuery4/Grammar.lean`: a nested direct element constructor also gets
  the namespace bindings declared by enclosing direct constructors
  (XQuery 3.1 §3.9.4, third rule; copy-namespaces mode does not apply to a
  new element). Tests: `id-transform-expr-052`, `propagateNamespaces02`.
  `Cfg.revalidation` for copy modify in library modules.
- `XQuery4/Module.lean`: `declare updating function`, `%updating`/`%simple`
  (XUST0032, XUST0033), `declare revalidation` (XUST0003), `fn:put` in
  the static function check, the update grammar.
- `XQuery4/Runtime.lean`: the `upd-` tags go to `XQueryUpdate.evalUpd`;
  `fn:put`.
- `XPath4/Eval.lean`: an updating function's return type is checked on
  its XDM instance only (3.0 §4.2); XUDY0038.
- `XPath4/Parser.lean`: an unprefixed type name in `element(N, T)` and
  `attribute(N, T)` is in the default namespace for elements and types
  (XQuery 3.1 §2.1.1); `transform with`.
- `XSD11/Load.lean`: `validateFor` refuses duplicate ID values under the
  validation root (XSD 1.1 §3.17.4, cvc-id).
- `Harness/Qt4Run.lean`: feature `XQUpdate`; test cases with several
  `<test>` queries run in order on the documents the earlier query left,
  with the first source document as the context value of the later ones;
  the assertions see the documents after the updates (`fn:put`); the
  result serializer writes `xmlns=""` where an unprefixed element in no
  namespace is under a default namespace; sources in ISO-8859-1; the
  revalidation modes as a per-test setting.

## Theorems

`XQueryUpdate/Theorems.lean` (no `sorry`, standard axioms only):
`docOfXT_wf`, `applyDoc_wf`, `applyDoc_parent_lt`, `applyDoc_children`
(a document after `applyUpdates` has the node-table invariants of a parsed
document, `XPath4/DocTheorems.lean`), `applyUpdates_nil` (the empty list is
the identity), `splitPul_noPul`, `flatU_true_eq_flatXT` and
`docOfXT_nodes_eq_flatXT` (copy modify and `fn:update` share the table
builder), and 7 `#guard` agreements of copy modify with `fn:update`. Open:
https://github.com/danbri/factoidal/issues/1178.

## Not done

- Static typing: the [2026-10-29 configuration](2026-10-29-static-typing.md)
  passes all 27 `upd-StaticTyping` tests. Wider inference and ordered mixed
  insertion-source types remain under https://github.com/danbri/factoidal/issues/1177.
- 6 tests with defective expected XML (whitespace):
  https://github.com/danbri/factoidal/issues/1176.
- Node identity across a snapshot (a rebuilt document has new indices).
