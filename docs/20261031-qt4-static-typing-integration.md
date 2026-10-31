# Static typing recovery against the current XML engine

This candidate recovers [PR263](https://github.com/danbri/factoidal-core/pull/263)
head `eddfd724ae190bca8378ce101ab8f0e2b5ab7296` onto release candidate
`542730da`, on `claude/qt4-static-typing-integration`. QName PR278 remains
separate. The frozen 0.28 source is not modified.

The analyser is opt-in (`FeatureSettings.staticTyping` defaults to false).
It reuses the engine's sequence types, subtype/conversion checks, function
catalogue, schema hooks and update operand rules. It checks branches and
function bodies independently of runtime selection. Unmodelled forms and the
existing expression/type fuel approximations do not establish whole-language
static-typing completeness. The original kernel theorem remains limited to
its stated literal/sequence/conditional fragment; it is not a theorem about
all XPath or XQuery expressions.

The source merge preserves current Harness configuration and confined URI
registry loading, XQuery reference handling (`xqRefs`), XML 1.1 settings,
named-type loading and private-annotation checks. New settings are propagated
through the grammar extension instead of resetting there.

## Recursion audit repair

The recovered source builds and passes its original checks, but the compiled
recursion gate found eight unclassified declarations. The FLWOR clause walk
was recursive in clause count. It now iterates through clauses and retains a
stack of deferred type transformations. Deferred let validation still follows
the remainder; for/where cardinality transforms still apply from the return
expression outward. Seven public query controls passed before this refactor,
including the FORG0006 precedence of an invalid where clause over a deferred
invalid let binding. These controls and update error ordering are build guards.

Node-test union traversal now has an enforced 1000-level budget and reports
FOER0000 on exhaustion, rather than silently accepting an unknown type. Its
zero/one/two-budget controls check that boundary. The other six recursive
helpers already decrease explicit fuel on type/expression nesting, entered
with 100 for type checks or 1000 for expression inference. The seven exact
semantic-depth classifications name these bounds and their tests. There is no
allowance for the removed clause-list recursion and no claim of arbitrary-depth
C-stack safety. The pre-existing approximations at exhausted budgets remain
explicit in the analyser and boundary tests.

## Measurement and reachability

The current tracked fixture inventory contains exactly 104 positive
`staticTyping` cases across 17 sets. The prechange binary built at `8638e566` (before the static-typing recovery)
marks all 104
unsupported. The final recovered engine passes all **104 / 0 / 0** targets,
including after the recursion repair. The 17 whole sets change from **1312 pass /
3 fail / 147 unsupported** to **1416 / 3 / 43**, both out of **1462**. All three
unrelated failures and 43 unsupported cases remain visible. These counts cover
these 17 sets, not the full catalogue.

The final named build (`StaticTypingTests`, `StaticTypingTheorems`, `l4qt4`)
passes 383 jobs. There are 104 executable guards in the two new check modules:
84 from the original implementation plus 20 integration/budget/order guards.
Both fragment theorems retain only propext, Classical.choice and Quot.sound.
The scoped generated-C recursion and csimp gates pass for the eleven changed
producer modules. No blanket module allowance was added: the seven entries
name actual fuel-bounded definitions, and the emitted C has no recursive
`infer.clauses` symbol.

The seven independent FLWOR controls, forced through the extension path by
count/group clauses, pass before and after the iteration repair. Their outputs
and error codes are unchanged. The update-error ordering control is also a
build guard. No test membership or exclusion list was changed.

Settings are reachable from the public Lean Env entry points and the QT4
harness. Current WASM/npm/CLI options do not yet expose staticTyping; thin
validated option wiring and consumer tests are a separate next step. Language
version PR262 and XSD configuration PR264 are not included here. Their remaining
unsupported scenarios must stay outstanding until those configurations run.

Logs and membership inventory are `/private/tmp/qt4-static-targets-current.json`,
`/private/tmp/qt4-static-{baseline,after,final}/*.log`,
`/private/tmp/qt4-static-integration-build-green.log`,
`/private/tmp/qt4-static-flwor-{before,after}.log` and
`/private/tmp/qt4-static-tail-audit-final.log`. The original dated worknote describes
its older baseline; this record supplies the current integration evidence.

The obsolescence sweep changes “all-enabled” wording to “default” where the new
opt-in feature made that phrase inaccurate. Existing theorem names remain
compatible. No fixture is deleted, excluded or reclassified; no new axioms,
sorry, native_decide, unsafe or partial definitions are introduced.
