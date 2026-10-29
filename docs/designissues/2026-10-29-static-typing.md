# Selectable XPath and XQuery static typing

The processor exposes `FeatureSettings.staticTyping`, default `false`.
`XPath4.evalConfigured` checks the expression before evaluation when the
setting is true. `evalString` uses that entry point. XQuery's `checkModules`
checks global initializers, function bodies and module bodies before binding
or evaluation. XQuery Update uses the same module check before updates.
The QT4 runner selects the setting from `feature=staticTyping`, including
negative dependencies. It does not select errors by test name or expected result.

This implements a fragment of the Static Typing Feature of XPath and XQuery
4.0 §2.3.3 and the operand rules of XQuery Update §5. It is not a claim of
complete static typing for either language. The measured targets and remaining
limitations are in [REPORT.md](../../REPORT.md).

## Shared implementation

`XPath4/StaticTyping.lean` uses the existing `IType`, occurrence indicators,
`Core.subtype`, atomic type derivation, function signature catalog and schema
hooks. It infers branch unions and concatenation cardinality, propagates
variable and focus types, checks function operands, and checks axis results.
Analysis visits both conditional branches and uncalled function bodies.
The existing `XQuery4/Static.lean` still supplies name and scope checks.

`XQueryUpdate/TypeRules.lean` checks inferred update operand types. It imports
only `XPath4.Core`, so XPath's type analysis can call it without an import
cycle through XQuery evaluation. Node kinds and occurrence checks share the
existing sequence-type relation. These checks include insertion ordering
constraints, insert/replace/rename target types, node-only deletion and
singleton-node copy sources.

The schema atomization check uses `SchemaHook.typeInfo` from the existing
XSD 1.1 integration. A typed element with mixed content can have a derived
element-only type with no typed value; static `data` analysis reports
`FOTY0012` for this case. No XML parser or XSD validator is duplicated.

## Static context and declarations

`Env.staticVars` and `Env.staticFocus` carry host declarations. The QT4 host
declares a loaded source to be a document node. The analyser does not inspect
its children or sample an evaluated value to decide an expression's type.
An explicit XQuery variable type takes precedence over the host declaration;
an unannotated external variable can use the supplied static type.

The existing AST uses `item()*` both for an omitted let annotation and for
an explicit `as item()*`. In static mode the parsers retain the latter by
wrapping its initializer in `treat as item()*`. This is an identity check on
values and gives the analyser the declared broad type. Default-mode parsing
keeps the previous AST. Module variables separately record which annotations
were omitted, including explicitly broad global and external variables.
`Cfg.features` also passes the setting to the XQuery grammar extension's
`runP`; otherwise that extension creates a new context with default settings.

## Proof boundary

`evalConfigured_staticTypingOff` proves by `rfl` that disabling the setting
leaves the evaluator unchanged. The existing `eval_allFeaturesEnabled` and
`Env.restrictFeatures_allEnabled` theorems remain checked.

`StaticTyping.fragment_sound` connects the actual `infer`, actual `eval`,
and public `Env.seqMatches`. Its syntactic fragment contains arbitrary atomic
literals, pairs of atomic literals, empty expressions, nested singleton
sequences, and nested conditionals with one literally empty branch. Tests of
these conditionals are unrestricted. Given sufficient inference fuel
(`sizeOf e < typingFuel`), successful evaluation matches the inferred type.
The theorem does not assume the matching conclusion as a premise.

The proof does not cover general variable, function, axis, FLWOR, map, array,
schema or update rules; parser correctness; or completeness of error detection.
Arbitrary concatenation and conditionals with two nonempty branches can form
nested choice types. A wider theorem needs a type-depth bound for the public
matcher, whose fuel is fixed at 1000, or a revised matcher. The two headline
axiom audits use only `propext`, `Classical.choice` and `Quot.sound`.

The proof and execution guards are imported by `Harness/Qt4Run.lean`, so
`lake build l4qt4` checks them without changing the library root.

## Remaining analysis limits

The inference walk is fuel bounded. Forms without a specific typing rule
return `item()*`; their operands are still checked. Unknown item types are
admitted by function conversion checks. This permits evaluation but does not
establish complete static type checking. General extension forms, precise
lookup types, user-function result inference, schema derivation and dynamic
function checks require further rules.

`IType` stores alternatives and occurrence indicators, but not sequence
ordering. An insertion source with multiple items of mixed attribute and
child-node types cannot establish the required attribute-prefix order in
this representation. Such a source is conservatively rejected, including
some valid ordered sources. The update work remains tracked by
https://github.com/danbri/factoidal/issues/1177 (static typing).

No network operation, commit or push is part of this task. Measurements and
implementation progress are recorded in the
[dated worknote](../20261029-static-typing.md).
