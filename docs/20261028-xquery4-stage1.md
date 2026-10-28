# XQuery 4.0 in Lean, stage 1

Date: 28 October 2026. Issue: https://github.com/danbri/factoidal/issues/1101
(XQuery 4.0 on top of the XPath 4.0 engine). XPath 4.0 stages:
[`20261027-xpath4-stage1.md`](20261027-xpath4-stage1.md),
[`20261028-xpath4-stage2.md`](20261028-xpath4-stage2.md). Target release: 0.21.0.

Sources: XQuery 4.0 editor's draft
(https://qt4cg.org/specifications/xquery-40/xquery-40.html, qtspecs
`b4723ff52fd9d4fabf2b4cd33bd44f21939c512c`), qt4tests
`b39c4bc027a56c82407f479709bc59e2122be5fc` (the copy in
`third_party/testing/qt4tests/`).

## How XQuery sits on XPath 4.0

XQuery 4.0 is XPath 4.0 plus a prolog, more expression forms and node
constructors. The Lean code keeps one parser and one evaluator for both
languages and adds three small hooks to `L4Factoidal/XPath4/`:

| Hook | File | What it does |
| --- | --- | --- |
| `ExtGrammar` in `PCtx.ext` | `XPath4/Parser.lean` | the parser tries the extension at every ExprSingle and every PrimaryExpr, before its own rules; the extension calls back into the XPath parser through `SubParsers`. `PCtx.ext` is `none` for XPath, so the XPath grammar is unchanged. `PCtx.types` holds the prolog's named item types. |
| `Expr.ext tag es ts qs ss` | `XPath4/Syntax.lean` | one constructor for every XQuery construct; `eval` gives it to `XQuery4.Runtime.evalExt` with a callback into `eval`, so the new code adds no recursion over expressions and spends the same fuel. |
| `XQuery4.callUser?`, `XQuery4.refUser?` | `XPath4/Eval.lean` | a static call or a named function reference whose name has no built-in function looks for a function declared in the prolog. |

The XQuery tree `formal/lean4/L4Factoidal/XQuery4/`:

| File | Content |
| --- | --- |
| `Runtime.lean` | node constructors (element, attribute, text, comment, processing instruction, document, namespace) with the content rules of §4.12.1.3; FLWOR tuple streams (`for ... allowing empty`, `count`, `order by`, `group by`, tumbling and sliding windows, `while`); `try`/`catch`/`finally`; `typeswitch`; `switch`; user function calls with keyword arguments and default values computed in the focus of the call |
| `Grammar.lean` | the XQuery productions: FLWOR, `switch`, `typeswitch` (both also with braces), `try`, direct constructors (attributes, namespace declarations, enclosed expressions, CDATA, references, boundary whitespace), computed constructors (also with a QName literal), `ordered`/`unordered`, extension expressions, string constructors, `validate` (raises XQST0075) |
| `Static.lean` | static checks: every variable reference has a binding in scope (XPST0008), every static call names a known function (XPST0017) |
| `Module.lean` | version declaration, prolog, main and library modules, `import module`, global variables in dependency order (a cycle is XQDY0054), `declare type`, `declare record` with its constructor function, decimal formats |
| `Theorems.lean` | the theorems below |

A constructed node is a new runtime document (`NodeRef.rt`, from XPath
stage 2). Its subtree is copied from the source document by index
arithmetic in one loop (a subtree is the index range `[i, last i]`).

Neither tree is imported by the library root `L4Factoidal.lean`: the
wasm and the npm package do not change.

## Measured result

Commands (from `formal/lean4/`, with `ulimit -s 65520`):

    lake build l4qt4
    .lake/build/bin/l4qt4 --isolate 60 --lang xquery
    .lake/build/bin/l4qt4 --isolate 60

`--lang xquery` applies the XQuery dependency filter (`XQ10+` to `XQ40`)
in place of the XPath one, binds the environment parameters that the
query declares `external`, and gives the evaluator the library modules
that a test case names. Same catalogue, same six families.

XQuery 4.0:

| Family | Pass | Fail | Unsupported | Total |
| --- | ---: | ---: | ---: | ---: |
| prod | 12215 | 1381 | 1352 | 14948 |
| op | 4521 | 106 | 162 | 4789 |
| fn | 12609 | 3562 | 1672 | 17843 |
| map | 347 | 11 | 3 | 361 |
| array | 475 | 49 | 13 | 537 |
| math | 181 | 0 | 0 | 181 |
| **Total** | **30348** | **5109** | **3202** | **38659** |

Of the tests that apply in XQuery mode (pass + fail = 35457), 85.6% pass.
Two test sets stop at the 60 s limit (`fn-fold-left` at `fold-left-024`,
`op-same-key` at `same-key-023`; the unfinished tests count as fail).

XPath 4.0 mode, before (stage 2) and after:

| Family | Pass before | Pass after | Fail after | Unsupported |
| --- | ---: | ---: | ---: | ---: |
| prod | 7856 | 7870 | 893 | 6185 |
| op | 3710 | 3712 | 75 | 1002 |
| fn | 11613 | 11620 | 3284 | 2939 |
| map | 342 | 342 | 11 | 8 |
| array | 450 | 450 | 41 | 46 |
| math | 181 | 181 | 0 | 0 |
| **Total** | **24152** | **24175** | **4304** | **10180** |

No XPath test set lost a pass (compared set by set). The 23 new XPath
passes come from two parser fixes (`local:function()` was read as an
inline function; `if#1` and the other reserved names are now XPST0003 in
a function reference) and two runner fixes (`assert` takes the effective
boolean value, as the catalogue says; `assert-xml` with the expected
markup written as escaped text).

Where the XQuery failures are: most are in functions and XPath 4.0
features that are not XQuery-specific (the regex engine in
`fn-matches.re`, `fn:serialize`, `fn:update`, `fn:element-to-map`,
`fn:map-to-element`, CSV, JNodes in `prod-PathExpr.J` and
`prod-AxisStep.J`, composite casts). The XQuery-specific sets with the
most failures are `prod-NamedRecordTypeDecl` (59; named record types
are structural here, the 4.0 draft makes a coerced map an instance of
the named type), `prod-FunctionDecl` (42), `prod-ModuleImport` (32),
`prod-ItemTypeDecl` (31), `prod-WindowClause` (24),
`prod-DefaultNamespaceDecl` (24), `prod-Annotation` (24).

## Theorems (`XQuery4/Theorems.lean`)

Proved, no `sorry`, axioms `propext`, `Classical.choice`, `Quot.sound` only:

* `mkFlwor_simple`, `flwor_for`, `flwor_for_at`, `flwor_let`,
  `flwor_where`: the parser builds every FLWOR through `mkFlwor`, and a
  FLWOR of `for`, `let` and `where` clauses only is the nested XPath 4.0
  `for`/`let`/`if` expression (`where` is a conditional with the empty
  sequence in the else branch).
* `eval_flwor_for`, `eval_flwor_let`: so XQuery `for ... return` and
  `let ... return` evaluate as the XPath `for` and `let` expressions, in
  every dynamic context and at every fuel.
* `lookupVar_markStatic`: the marker binding that the module evaluator
  puts on top of the bindings hides no variable of the query.
* `bindModules_empty`, `evalModule_emptyProlog`: a main module with an
  empty prolog is the static check of its body followed by
  `XPath4.eval` of the body. So an XPath expression run as an XQuery
  main module is evaluated by the XPath 4.0 evaluator.

Tested (`#guard` in `XQuery4/Module.lean`, and the qt4tests), not
proved: constructors, the tuple-stream clauses, `try`, `typeswitch`,
`switch`, user functions.

Open:

* Every node a constructor builds serialises to well-formed XML (the
  `XML.Node.wellFormed` and `Node.serialize_*` theorems): needs a map
  from the node table to `XML.Node` and loop invariants over
  `Runtime.buildElement`.
* The tuple-stream FLWOR (`ext "flwor"`) of `for`/`let`/`where`
  clauses agrees with the nested XPath form.

## Not implemented

Node identity of constructed nodes is derived from the content, the
constructor and the bindings in scope; two constructions with equal
content in equal bindings get the same identity. Named record types are
structural (a map that has the fields is an instance). `fn:error` loses
the namespace and the value of the error (`$err:value` is empty, a catch
of `Q{uri}name` for a non-`err` namespace does not match). Schema import
and validation (XQST0009, XQST0075), `copy-namespaces no-preserve`,
`construction preserve`, `declare option` (read and ignored),
serialization parameters, the XQuery Update Facility, full text.
