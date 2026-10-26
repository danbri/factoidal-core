# Regex profiles and interval preconditions

The shared derivative matcher evaluates an internal regular-expression tree.
Its correctness for that tree does not establish that parsing a standards
expression produced the right tree. Admission, translation, matching and the
public caller require separate evidence.

## Specification edition and admission

The XSD 1.1 datatype caller uses `Regex.Profiles.compileXsd11`, defined in
`Regex/Xsd11.lean`. Its selected XML name tables are XML 1.0 Fifth Edition.
This is an explicit choice permitted by
[XSD 1.1 section H.1](https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/#impl-defined),
with the name escapes specified in
[section G.4.2.5](https://www.w3.org/TR/2012/REC-xmlschema11-2-20120405/#regexs).
The separate conservative XSD 1.0 profile remains unchanged.

The integration initially selected the 1.0 profile for the existing 1.1
caller. Correcting that choice recovered 255 scored fixture cases. It did
not justify admitting every escape handled by the legacy parser: that parser
uses ASCII digits for `\d` and ECMAScript word characters for `\w`, while
XSD specifies Unicode categories. Those escapes remain unsupported in this
profile. The remaining 2,820 fewer scored XSD cases are recorded as reduced
coverage, not passes or repaired conformance.

## A valid union was an invalid complement input

The XML NameChar table appends extra ranges to NameStartChar. Membership in
that union can be correct regardless of interval order. `complementRanges`
requires sorted, disjoint intervals. Supplying the appended table directly
made both `\c` and `\C` accept U+00B7, the middle-dot character.

The repair normalizes the table at the complement call. Controls check name
classes and their complements, non-ASCII witnesses, edition separation and
continued category refusal. A public SHACL test also reproduces the old
wrong answer. That test covers the shared parser's complement behavior; it
does not certify the entire SHACL regex implementation.

The missing assurance obligation was the representation precondition at the
caller. Neither a derivative theorem about the resulting tree nor successful
positive-class tests established it. Full normative parser adequacy remains
a separate proof obligation.

## Regression controls

The [semantic assurance specification](../semantic-assurance-spec.md) requires
edition preservation and interval preconditions. The
[integration record](../20261022-pr-integration.md) identifies source, native
suite and public artifact results. Original failures are preserved under
`docs/audits/`.

The same integration added proved iterative replacements for five flat-input
scans. Their [proof and generated-code review](../audits/integration-tail-20261022/20261022-integration-tail-review.md)
separates flat traversal from remaining expression/document nesting. PR CI
now runs both recursion and compiler-replacement reach gates and their
self-tests. Those checks do not prove stack safety for arbitrary nested
expressions or full standards conformance.
