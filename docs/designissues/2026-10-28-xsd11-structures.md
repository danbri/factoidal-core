# XML Schema 1.1 Structures in Lean (`L4Factoidal/XSD11/`)

Date: 2026-10-28. Tracking: https://github.com/danbri/factoidal/issues/1101
(QT4 staged implementation). PR: https://github.com/danbri/factoidal-core/pull/206.
Owner goal, 2026-10-28, verbatim: "Complete qt4cg.org and pass all its tests";
"bridge theorems to make sure our codebase is a network".

## Why

Many qt4tests and xslt40-test cases are schema-aware (`schemaImport`,
`schemaValidation`, `typedData`, typed nodes, `validate`, `import schema`,
`xsl:import-schema`). They need XML Schema 1.1 Part 1 (Structures,
https://www.w3.org/TR/xmlschema11-1/) on top of the Part 2 datatype code in
`L4Factoidal/XSD/`.

## How it works

The tree is outside the library root `L4Factoidal.lean`, so the wasm and the
npm package do not change.

| Module | What it does |
|---|---|
| `Components.lean` | Schema components (§3). Components refer to each other by index into arrays of their kind; global ones are also listed by expanded name. Index 0 is `xs:anyType`, 1+k the k-th Part 2 built-in, then `xs:error`, then user types. A simple type's value space is the Part 2 `XSD.SimpleType` in its `body`. |
| `Reader.lean` | Schema documents to components, pure. Four passes: collect top-level components of every document reached (`include`, chameleon include, `import`, `redefine`, `override`); give global types, elements and attributes their indices; build each component; finish (types from substitution group heads, Part 2 bodies along base chains, effective content and attribute uses of complex types). The XML namespace schema is built in. |
| `ContentModel.lean` | A particle as a regular expression with counted repetition; children consumed by derivatives. `all` is a shuffle (1.1). Open content. An element declaration takes precedence over a wildcard (1.1). Two rules keep the state small: `(x{a,b}){n,k} = x{n·a, b·k}` when `a ≤ 1`, and pruning of residuals that another residual subsumes. |
| `Validate.lean` | Assessment (§3.3.4, §3.4.4, §3.2.4, §3.17.4). Output is a PSVI tree `PNode`: the input plus `PInfo` (validity, type, declaration, nil, normalized and typed value). Defaulted attributes and default text are held apart. Type alternatives and assertions go through a `Hooks` value; with `Hooks.none` they are reported as unsupported, never guessed. |
| `Identity.lean` | `key`, `keyref`, `unique` with the restricted XPath of §3.11.6.2, over the PSVI. |
| `Constraints.lean` | Schema component constraints: circular derivation, `final`, extension and restriction (attribute uses, wildcards, content type restricts as language inclusion), UPA, EDC, `all` placement, value constraints, substitution groups, Part 2 §4.3 facet rules. |
| `SchemaForSchemas.lean` | Every schema document is validated against the schema for schema documents with the same validator (the suite's copy, `saxonData/Override/XMLSchema.xsd`). |
| `Pattern.lean` | Pattern facets: the shared XSD 1.1 regex profile first; for the XSD 1.1 syntax it refuses (`\d`, `\p{..}`, subtraction), the F&O 4.0 parser, with the 4.0-only syntax refused and `^`/`$` read as characters. |
| `XPathHooks.lean` | The PSVI as an XDM 4.0 document (`psviDoc`): `NRec.tann` (type annotation), `NRec.tval` (typed value), `NRec.nilled`. Assertions and type alternatives evaluated by `XPath4`. |
| `Load.lean` | File side: read schema documents and their closure, a per-process schema cache, `schemaHookOf` (in-scope schema definitions for XPath 4.0), `validatedDoc`. |
| `Theorems.lean`, `ShaclBridge.lean` | Bridge theorems (below). |

XPath4 hooks (small, in shared files):

- `XPath4/Syntax.lean`: `NRec.tann`, `NRec.tval`, `NRec.nilled`; `IType.elemT`,
  `attrT`, `schemaElem`, `schemaAttr`.
- `XPath4/Core.lean`: `SchemaHook` (type derivation, element and attribute
  declarations, substitution groups) as `Env.schema`; atomization reads
  `tval`; the four new item types match through the hook.
- `XPath4/Parser.lean`: `element(N, T?)`, `attribute(N, T)`,
  `schema-element(N)`, `schema-attribute(N)`.
- `XPath4/Lib.lean`: `fn:nilled` reads `NRec.nilled`.

With no schema the hook knows only the built-in types, and every node is
untyped, so XPath without a schema behaves as before.

## Hook for XSLT 4.0 and XQuery 4.0

`xsl:import-schema`, the `validation` attributes, `import schema` and
`validate {}` call:

- `XSD11.loadSchemaCached files : IO Schema` (or `readSchemaDocs` and
  `buildSchema` when the documents are already parsed),
- `XSD11.schemaHookOf s : XPath4.SchemaHook`, put into `Env.schema`,
- `XSD11.validatedDoc s doc : XPath4.Doc × Assessment` (strict), or
  `XSD11.assessRoot` with `How.wild .lax` for lax validation, then `psviDoc`.

## Theorems (no `sorry`, axioms propext, Classical.choice, Quot.sound)

- `validateElement_erase`, `assessRoot_erase`: validation does not change the
  infoset; erasing the annotations gives the input element.
- `validateSimple_ok`: an accepted literal is `XSD.validate`-valid for the
  type's Part 2 body and satisfies its pattern facets.
- `xsdPatternRe_shared`, `patternOk11_shared`: where the shared XSD 1.1 regex
  profile reads the patterns, the XSD11 pattern test is `XSD.patternMatches`.
- `valueOf_builtin`: a facet-free built-in is `XSD.lexicalMap` on the
  whitespace-normalized literal.
- `shacl_datatype_is_xsd`: SHACL `sh:datatype` (`SHACL.literalIllFormed`) and
  XSD11 agree for non-date/time, non-float built-ins.

## Measurements

From `formal/lean4/`: `lake build l4xsd11 && ulimit -s 65520 &&
.lake/build/bin/l4xsd11`. W3C suite `w3c/xsdtests` at 7bc3365c: see the PR
comments for the current numbers.

## Open items

- Runtime list recursions to loops: https://github.com/danbri/factoidal/issues/1151.
- `xpathDefaultNamespace` is not applied by the XPath 4.0 parser (no default
  element namespace), and an assertion's context element has a document node
  as parent (§3.13.4.1 asks for a parentless element).
- User-defined atomic types are annotated with their built-in base type in
  `XPath4.Atomic` (no user type in `AType`), so `instance of my:type` on an
  atomic value is not decided.
- A theorem that `XPath4.castFromString` accepts every literal that
  `XSD.valueOf` accepts for the same built-in is not proved.
