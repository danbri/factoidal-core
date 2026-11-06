# Fresh construction identity: diagnosis and allocation design

This is a design record, not an implementation or conformance gain. The
bounded-consumer change at `8638e566d12fa3059851c695156517cdd57f8357` retains
the visible QT4 `generate-08` failure: twenty newly constructed nodes collapse
to one identity. Do not rekey arbitrary callback results to fix that case.

## Existing behavior

`XQuery4.Runtime.newDocId` derives a document ID from the constructor kind,
content, source offset and `envSalt`. The salt summarizes position, context and
selected variable bindings. `XPath4.Eval.apply` evaluates a normal inline
function with its closure and parameters, absent focus and position zero.
Repeated zero-argument calls therefore have the same ID inputs, even when the
caller visits different iterations. The Runtime header already records this
limitation. It affects static user functions, module functions and tree-producing
library calls as well as `fn:generate`.

A constructor occurrence creates a new node; returning an already existing node
preserves its identity. See [XQuery 4.0 node constructors](https://qt4cg.org/specifications/xquery-40/xquery-40.html#id-constructors)
and [computed namespace construction](https://qt4cg.org/specifications/xquery-40/xquery-40.html#id-computedNamespaces).
A change that rekeys every callback result would break, for example,
`let $x := <e/> return generate($x, fn(){$x})[1 to 3]`: the three items must
retain the identity of `$x`.

## Fresh measurements

Existing binary built with the bounded-consumer patch; no new build or fixture
exclusions. All counts are pass / fail / unsupported:

| Official set | Counts | Identity failure |
| --- | --- | --- |
| fn-generate | 15 / 1 / 0 | generate-08 |
| op-is-same-node | 48 / 1 / 0 | cbcl-is-same-node-001 |
| op-is-not-same-node | 37 / 1 / 0 | is-not-303 |
| fn-update | 463 / 2 / 0 | fn-update-xnode-116 |
| prod-CompNamespaceConstructor | 49 / 2 / 1 | nscons-028 |

These are five confirmed identity failures in five sets, not an exhaustive
classification. The other two failures and older-language unsupported case
remain distinct. Logs: `/private/tmp/qt4-identity-*.log` and
`/private/tmp/qt4-generate-after.log`.

Seven local probes in `/private/tmp/qt4-node-identity-probes` score 5 pass / 2
fail. Repeated zero-arity construction and construction inside a loop fail.
Captured-node return, captured-node return in a loop/generator, different static
constructor offsets, and copied-child separation pass. Their log is
`/private/tmp/qt4-node-identity-probes.log`; they are diagnostic fixtures, not
additional official coverage.

## Required design

Use an explicit fresh-allocation supply shared by an entire query evaluation,
or a complete evaluation-occurrence address. Allocate only when construction or
copying actually creates a node/document. Existing nodes returned by closures,
variables, maps, arrays, generators and host functions retain their IDs. All
nodes of a single document retain a common document ID and their existing index
relationships; document-order comparisons must remain consistent.

A state supply requires the evaluator and its callback boundaries to propagate
allocation state. The relevant surface includes `eval/apply/callFn`, library
`Hooks`, XQuery `CallCb` and `ExtCb`, module evaluation, tree-producing library
functions, and update/copy producers. Errors caught by try/catch must not reset
the supply and reuse IDs of already observable nodes. Host inputs need a
separate/reserved identity domain. The public query API can keep an `Except`
result while an internal state transformer threads allocation.

An occurrence-address alternative must distinguish repeated applications and
loop/generator invocations even with identical arguments and closures. Merely
adding a caller position, more bindings, a hash salt, or a source offset does
not establish that property. Neither approach should use global mutable state,
`unsafe`, new axioms, partial definitions or result-wide rekeying.

Before integration, regressions must cover static and dynamic calls, callbacks
of arity zero/one/two, imported functions, nested construction, parse/update
producers, caught errors, existing-node preservation and nodes contained in maps
or arrays. Proof obligations should include freshness, preservation of existing
identity, and within-document reference consistency. This exceeds a bounded
release fix and remains implementation work.
