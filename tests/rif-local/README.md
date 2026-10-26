# Project-local RIF Core cases

Corrected copies of three W3C RIF Core positive entailment tests whose test
data is defective. Issue: https://github.com/danbri/factoidal/issues/1031
(three RIF Core W3C cases with defective data).

Owner, 2026-10-25, verbatim: "1 yes excude bad issues, create cleaned up.
Project-local unit tests to feplace them".

`lake exe l4rif` (run in `formal/lean4/`) reports the W3C originals as
`EXCLUDED <id>: defective test data, <issue URL>`, outside pass, fail and the
total, and runs these copies as the `rif-local` line. Every case here must
pass; the run exits non-zero if one does not. If a W3C original starts to
pass, the run also fails, and the exclusion in `defectiveData`
(`formal/lean4/Harness/RifRun.lean`) must be removed.

The layout is the layout of the W3C suite: one directory per test kind, one
per case, with `<id>-premise.rifps` and `<id>-conclusion.rifps`. Each
conclusion is a copy of the W3C file. Each premise is a copy of the W3C file
with only the changes below.

Originals: `third_party/testing/rif-core-suite/Core_v1.22/Approved/PositiveEntailmentTest/<id>/`
(published at https://www.w3.org/2005/rules/test/repository/tc/).

## EBusiness_Contract

Defect: the rule guards with `pred:is-literal-dateTime` (RIF-DTB §4.2) and computes
`func:subtract-dateTimes` (RIF-DTB §4.8.1.22), but the two facts are `xs:date`
literals (`"2008-07-22Z"^^xs:date`, `"2008-07-11Z"^^xs:date`). In XSD 1.1
Part 2, `xs:date` (§3.3.9) and `xs:dateTime` (§3.3.7) are distinct primitive
datatypes, and the value spaces of primitive datatypes are disjoint. The guard
is false, so the conclusion is not entailed.

Change (premise lines 33 and 34): the facts are `xs:dateTime` literals.

    cpt:delivered(ord:Order14 "2008-07-22T00:00:00Z"^^xs:dateTime stores:Store9)
    cpt:scheduled(ord:Order14 "2008-07-11T00:00:00Z"^^xs:dateTime)

The difference is `P11D`; `func:days-from-duration` gives 11, which is
greater than 10, so `cpt:reject(stores:Store9 ord:Order14)` is entailed.

## Builtins_Time

Defect: premise line 65 compares the result of
`func:add-dayTimeDuration-to-dateTime` with `"2000-11-02T12:27:00"^^xs:dayTime`.
XSD has no datatype `dayTime`. The function returns `xs:dateTime` (RIF-DTB
§4.8.1.37, adapted from the operator `op:add-dayTimeDuration-to-dateTime` of
XPath and XQuery Functions and Operators).

Change (premise line 65): `"2000-11-02T12:27:00"^^xs:dateTime`.

## Builtins_PlainLiteral

Defect: premise line 18 compares the result of `func:lang-from-PlainLiteral`
with `"en"^^xs:lang`. XSD has no datatype `lang`.

Change (premise line 18): the plain string `"en"`, which is `xs:string`.
`func:lang-from-PlainLiteral` (RIF-DTB §4.10.1.3, adapted from
`plfn:lang-from-PlainLiteral` of the rdf:PlainLiteral specification) returns
the language tag as a string, and the empty string for a literal with no tag.
Premise line 19 of the same W3C test expects `""` for that case; the empty
string is not in the lexical space of `xs:language`, so `xs:string` is the
return type that agrees with both lines. The Lean implementation returns
`xs:string` (`L4Factoidal/RIF/Builtins.lean`, case `"lang-from-PlainLiteral"`,
and its `#guard` tests).

Section numbers checked against https://www.w3.org/TR/rif-dtb/ (RIF Datatypes and Built-Ins 1.0, Second Edition) on 2026-10-25.
