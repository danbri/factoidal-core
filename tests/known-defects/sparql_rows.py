#!/usr/bin/env python3
"""Print the solutions of a SPARQL SELECT result as canonical text lines.

Reads SPARQL Query Results XML (a W3C `.srx` file) or SPARQL Query Results
JSON on standard input and writes one line per solution, sorted. A line lists
the bound variables in name order as `?var=term`, separated by one space; a
solution with no bound variable is written `(no bindings)`. Terms:

  IRI                 <iri>
  blank node          _:b   (labels are not compared: SPARQL 1.1 18.1.8
                            makes two solutions equal up to blank node
                            renaming, and this tool does not search for the
                            renaming)
  literal             "lexical form"  followed by ^^<datatype> or @tag;
                      a datatype of xsd:string is left out (RDF 1.1 Concepts
                      3.3: a simple literal is an xsd:string literal)

Two result sets that give the same lines have the same solution mappings,
including the same domains (SPARQL 1.1 18.1.8: equal mappings have equal
domains), which a comparison that only checks the expected variables would
not detect.

Usage:  python3 -I sparql_rows.py < results.srx
        python3 -I sparql_rows.py < results.json
Exit 0 and the lines on success; exit 1 with a message on stderr when the
input is neither a SELECT result in XML nor in JSON.
"""
import json
import sys
import xml.etree.ElementTree as ET

XSD_STRING = "http://www.w3.org/2001/XMLSchema#string"
SRX = "{http://www.w3.org/2005/sparql-results#}"


def literal(lexical, datatype, lang):
    text = json.dumps(lexical, ensure_ascii=False)
    if lang:
        return text + "@" + lang
    if datatype and datatype != XSD_STRING:
        return text + "^^<" + datatype + ">"
    return text


def rows_from_json(text):
    doc = json.loads(text)
    solutions = []
    for binding in doc["results"]["bindings"]:
        terms = {}
        for var, term in binding.items():
            kind = term["type"]
            if kind == "uri":
                terms[var] = "<" + term["value"] + ">"
            elif kind == "bnode":
                terms[var] = "_:b"
            elif kind in ("literal", "typed-literal"):
                terms[var] = literal(term["value"], term.get("datatype"),
                                     term.get("xml:lang"))
            else:
                raise ValueError("unknown term type " + kind)
        solutions.append(terms)
    return solutions


def rows_from_xml(text):
    root = ET.fromstring(text)
    results = root.find(SRX + "results")
    if results is None:
        raise ValueError("no results element (not a SELECT result)")
    solutions = []
    for result in results.findall(SRX + "result"):
        terms = {}
        for binding in result.findall(SRX + "binding"):
            var = binding.get("name")
            node = list(binding)[0]
            tag = node.tag.replace(SRX, "")
            if tag == "uri":
                terms[var] = "<" + (node.text or "") + ">"
            elif tag == "bnode":
                terms[var] = "_:b"
            elif tag == "literal":
                terms[var] = literal(
                    node.text or "", node.get("datatype"),
                    node.get("{http://www.w3.org/XML/1998/namespace}lang"))
            else:
                raise ValueError("unknown term element " + tag)
        solutions.append(terms)
    return solutions


def main():
    text = sys.stdin.read()
    try:
        if text.lstrip().startswith("{"):
            solutions = rows_from_json(text)
        else:
            solutions = rows_from_xml(text)
    except Exception as err:  # any malformed input is the caller's ERROR
        print("sparql_rows.py: " + str(err), file=sys.stderr)
        return 1
    lines = []
    for terms in solutions:
        if terms:
            lines.append(" ".join("?%s=%s" % (v, terms[v]) for v in sorted(terms)))
        else:
            lines.append("(no bindings)")
    for line in sorted(lines):
        print(line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
