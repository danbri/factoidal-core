#!/usr/bin/env python3
"""Find cross-family Lean helper-name collisions and direct shared imports.

Review aid, NOT a Lean parser, semantic clone detector or conformance checker.
Comments and literals are masked before scanning ordinary def/abbrev/import
commands. Macros, quoted identifiers and generated declarations are not modelled.
Matching names can be intentional wrappers; differently named duplicates may be
missed. Imports establish availability, not actual use or normative dependence.
Selected semantic identifiers are inventoried with source lines for reviewing
mixed equality/conversion policies. Mentions include declarations and are not
name-resolved calls; field notation and unrelated names can be ambiguous.
"""
import argparse
import json
from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SEMANTIC = re.compile(
    r"hex|base64|digit|decimal|integer|lexical|date|time|leap|duration|"
    r"regex|pattern|escape|iri|uri|namespace|qname|space|utf|unicode|sameTerm|termEqual|promoteLiteral|"
    r"round|floor|ceil|numeric|langMatches", re.I)
SHARED = (
    "Encoding.Hex", "XSD.Datatypes", "XSD.Lexical", "XSD.ValueSpace", "Regex.Profiles",
    "Regex.XPath", "Regex.Ecma", "XML.NamespaceView", "XML.Namespaces", "Syntax.IriResolve",
    "JSON.Parser", "Fn.String", "Fn.Numeric", "Fn.Comparison", "Fn.Arithmetic",
    "Fn.Rounding", "Fn.NumericUnary", "Fn.Cast", "RDF.TermIdentity",
    "CSVW.Diagnostics",
    "RIF.Matching", "RIF.RdfMapping", "Harness.RifImport",
)
SEMANTIC_IDENTIFIERS = (
    "sameTerm", "eqb", "termEq", "literalPromote", "promoteLiteral",
    "erEqual", "erTermEqual", "sparqlOrder", "toTerm?", "toNumeric?",
    "parseDateTimeFor", "parseIntegerLex", "parseDecimalLex",
    "literalCompare", "termCompare", "relationalCompare", "dateTimeOrder",
    "numericCompare", "numericValueCompare", "numericEquality", "numericValue?", "numericDatatype",
    "isNumericDatatype", "isNumericOperand", "numericLexicalEbv",
    "parseToScaled", "parseDoubleToScaled", "decimalOrScientific",
    "lexicalValue?", "literalValue?", "booleanValue?", "fnIsNumeric", "castBoolean",
    "evalArithmetic", "sumNumeric", "avgNumeric", "floatingValue", "roundRational",
    "numericLiteralEqual", "evalNumericUnary", "numericResult", "integralFloating",
    "integralN", "integral", "floorN", "ceilingN", "roundN", "lexFloor", "lexCeil", "lexRound",
    "dtValue", "dtSeconds", "canonicalSeconds", "extractSecondsField",
    "langMatchesBasic", "fnLangMatches", "langMatchesNe", "simpleLiteral?", "sparqlApply",
    "regexCore", "replaceCore", "compileSearch", "matchSparql", "replaceSparql",
    "quoteReplacement", "erStringPreserve", "direction?",
    "regexReplace", "replaceLoop", "cmatch", "longestEnd", "pickCaps", "atStart", "atEnd",
    "eraseAssertions", "anchoredPrefix",
    "spaceRanges", "regexMatch", "matchesPattern", "patternMatch", "formatConvert",
    "applyRegexFormat", "regexFormatWarning", "definitelyMalformed", "prepareLexical",
    "finishConversion", "tableRegexWarnings", "tableConversionIssues", "inLexicalSpace",
    "xsdFamily", "numericLex", "boolValue", "isLiteralOf",
    "isLiteralNotOf", "literalGuard", "checkedLexicalValue", "valueInBuiltin",
    "lexicalValueInBuiltin", "valueInSpace",
    "literalNotIdentical", "valIdentical", "valEqualOrIdentical", "dtIdentical",
    "groundMatch", "groundMatches", "matchResult", "gOfTerm", "termOfG", "factsOfTriple",
    "graphMappingSupported", "completeGraph?", "saturateGraph", "rifSaturateDataset",
    "numericArithmetic", "numericIntegerDivide", "numericMod", "cmpNum",
    "decimalIntegerDivide", "decimalMod", "floatingIntegerDivide", "floatingMod",
    "castXsd", "castNumeric", "castValue?", "floatingDecimal", "narrowDouble",
)
IDENTIFIER = re.compile(r"[\w'][\w'.?]*")
DECL = re.compile(
    r"^[ \t]*(?:@\[[^\n]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe)[ \t]+)*"
    r"(?:def|abbrev)[ \t]+([\w'.?]+)", re.M)
IMPORT = re.compile(r"^[ \t]*import[ \t]+([^\n]+)", re.M)
CHAR = re.compile(r"'(?:\\(?:[nrt0\\'\"]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^'\\\n])'")


def code_only(source):
    """Mask nested Lean comments, strings and character literals; keep offsets."""
    out = list(source)
    i, depth = 0, 0
    while i < len(source):
        start = i
        if source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i = min(i + 2, len(source))
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        elif source[i] == "'" and (match := CHAR.match(source, i)):
            i = match.end()
        else:
            i += 1
            continue
        for j in range(start, i):
            if out[j] != "\n":
                out[j] = " "
    return "".join(out)


def audit(root, all_names=False, include_harness=False):
    base = root / "formal/lean4/L4Factoidal"
    paths = sorted(base.rglob("*.lean"))
    if not paths:
        raise ValueError(f"No Lean sources under {base}")
    if include_harness:
        paths += sorted((root / "formal/lean4/Harness").rglob("*.lean"))
    declarations, consumers, mentions = defaultdict(list), defaultdict(list), defaultdict(list)
    count = 0
    for path in paths:
        # Runtime sources only: test/proof mirrors otherwise dominate the list.
        if re.search(r"Tests?|Theorems?|Proofs?|Refinement", path.stem):
            continue
        count += 1
        source = path.read_text(encoding="utf-8")
        code = code_only(source)
        relative = path.relative_to(root).as_posix()
        family = path.relative_to(base).parts[0] if path.is_relative_to(base) else "Harness"
        for line, text in enumerate(code.splitlines(), start=1):
            # Keep the spelling: `Term.eqb` and `value.eqb` deserve different
            # review even though neither can be resolved by this scanner.
            for spelling in sorted(set(IDENTIFIER.findall(text))):
                identifier = spelling.rsplit(".", 1)[-1]
                if identifier in SEMANTIC_IDENTIFIERS:
                    mentions[identifier].append(dict(spelling=spelling,
                        family=family, file=relative, line=line))
        for match in DECL.finditer(code):
            name = match.group(1)
            key = name.rsplit(".", 1)[-1].rstrip("?")
            if all_names or SEMANTIC.search(key):
                line = code.count("\n", 0, match.start()) + 1
                declarations[key].append(dict(name=name, family=family,
                    file=relative, line=line))
        for match in IMPORT.finditer(code):
            for module in match.group(1).split():
                if module.startswith(("L4Factoidal.", "Harness.")):
                    consumers[module.removeprefix("L4Factoidal.")].append(
                        dict(family=family, file=relative))
    candidates = [dict(name=name, families=sorted({d['family'] for d in sites}),
                       declarations=sites)
                  for name, sites in declarations.items()
                  if len({d['family'] for d in sites}) > 1]
    candidates.sort(key=lambda row: (-len(row['families']), row['name']))
    return dict(schema_version=1, source_modules=count,
        scope="ordinary runtime def/abbrev names; tests/proof files excluded",
        includes_harness=include_harness,
        limitations=__doc__.strip(), candidates=candidates,
        shared_direct_imports={name: consumers[name] for name in SHARED},
        semantic_mentions={name: mentions[name] for name in SEMANTIC_IDENTIFIERS})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--all-names", action="store_true",
                        help="Include generic names, beyond semantic helper keywords")
    parser.add_argument("--include-harness", action="store_true",
                        help="Also inspect harness code for duplicated parsing/comparison policy")
    parser.add_argument("--output", type=Path, help="Write JSON instead of stdout")
    args = parser.parse_args()
    result = json.dumps(audit(args.root, args.all_names, args.include_harness), indent=2) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
