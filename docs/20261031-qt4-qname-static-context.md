# Static namespace capture for parse-QName function items

The candidate on `claude/qt4-qname-static-context` is based on release candidate
`542730da`. It uses the bounded-generator patch unchanged.

The failing QT4 `parse-qname-101` loads a library module whose exported global
variable holds `fn:parse-QName#1`. A later call must resolve the module's prefix
bindings, rather than those of its caller. The prior bare built-in function
item retained only name/arity and therefore raised FONS0004.

[F&O 4.0 §10.1.2](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-parse-QName)
identifies the namespace dependency. `XPath4.Lib.builtinRef` now gives only
`fn:parse-QName#1` an inline callable carrying the existing module-context
namespace entry and function-name metadata. Named references, lookup and
partial-application construction share that helper. Other built-in references
keep their representation. Closure bindings include only lexical namespace
bindings, with no static marker or globals: caller late bindings cannot supply
an absent prefix. Existing module closure application restores the captured
namespace table. No new function representation or context fields are needed.

The same specification makes an unprefixed NCName a QName in no namespace,
regardless of a default element namespace. The direct library branch now
implements that rule. URI-qualified-name parsing is unchanged.

Sixteen reachable executable guards cover module returns by named reference,
function lookup and placeholders, a conflicting caller prefix, a caller-only
prefix, default element namespaces, name/arity metadata, empty/invalid/wrong-type
arguments, and a lexical namespace-variable override. `FeatureTests` imports
the new `QNameContextTests` module. These checks are not equivalence proofs.

Validation on macOS arm64:

- Named `lake build L4Factoidal.XPath4.QNameContextTests l4qt4` passes (377
  jobs), including all sixteen new guards and the existing feature guards.
- Official `fn-parse-QName`: **19 pass / 1 fail / 0 unsupported → 20 / 0 / 0**.
- Fresh before/after controls are unchanged: `fn-function-lookup` **680 / 0 / 4**;
  `fn-function-name` **28 / 1 / 1**; `fn-function-arity` **21 / 0 / 2**;
  `fn-load-xquery-module` **181 / 1 / 2**. These existing failures and all
  unsupported cases remain outstanding, including static typing and older modes.
- `fn-generate` remains **15 / 1 / 0**, with `generate-08` still failing.

Scoped compiled-C tail-recursion and csimp reachability gates pass for the
regenerated `XPath4/Lib.c` and `XPath4/Eval.c`, with existing allowances unchanged.
No axioms, `sorry`, `native_decide`, partial definitions or dependencies were added.

All twenty official parse-QName cases retain their fixture membership and
scoring. The unchanged fixture SHA-256 is
`484d37fd5faa6697f14506f189b75e2af7678aca5431d77cf947554a0a7367d5`. No fixture or harness was changed. Logs are
`/private/tmp/qt4-qname-context-build-green.log`, `/private/tmp/qt4-qname-fn-*.log`
and `/private/tmp/qt4-qname-before-fn-*.log`; compiled audit output is
`/private/tmp/qt4-qname-tail-audit.log`. The two earlier build attempts
caught test scaffolding mistakes (an import name and a reserved helper
identifier); the final build above succeeds.

The obsolescence sweep found no current namespace-capture claims in docs needing
retraction; historical catalogue measurements remain dated. Fresh-node identity
is separate design work and the remaining generator failure stays visible.
