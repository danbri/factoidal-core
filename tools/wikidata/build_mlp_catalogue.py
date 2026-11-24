#!/usr/bin/env python3
"""Build a versioned catalogue from pinned Wikimedia revision snapshots.

This runs the local Java rewriter and, optionally, the Lean parser. It does
not submit queries to either public WDQS endpoint.
"""

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
import re
import subprocess
from tempfile import NamedTemporaryFile

from compare_mlp import CORPUS, ROOT, run_lean


# The historical harvest recognises SPARQL and SPARQL2. The collections
# revision contains one query in a misspelt SPARFQL template.
TEMPLATE = re.compile(
    r"\{\{\s*(SPARQL2?|SPARFQL)\s*\|\s*query\s*=([\s\S]*?)(?<!\S)\}\}[ \t]*$",
    re.IGNORECASE | re.MULTILINE,
)
HEADING = re.compile(r"^(={2,6})\s*(.*?)\s*\1\s*$", re.MULTILINE)
QUOTED = r"""(?:"{3}[\s\S]*?"{3}|'''[\s\S]*?'''|"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*')"""
TOKEN = re.compile(
    rf'{QUOTED}|<[^<>"{{}}|^\x60\\\s]+>|\#[^\r\n]*|[?$]\w+|(?:\w+)?:[\w-]*|[a-zA-Z_][a-zA-Z_0-9-]*|[^\s]'
)
LANGUAGE_PARAM = re.compile(
    r"""(\bwikibase:language\s*)(["'])([^\r\n]*?)\2""", re.IGNORECASE
)
WIKI_PIPE = "{{!}}"
AUTO_LANGUAGE = "[AUTO_LANGUAGE]"
LEAN_LANGUAGE_MARKER = "qaa-x-factoidal-auto"
QUERY_FORMS = {"select", "ask", "construct", "describe"}
PAGES = CORPUS.with_name("pages.json")

SUBPAGE_DOMAINS = {
    "botany": "Botany",
    "booker": "Literature and publishing",
    "calendars": "Calendars",
    "collections": "Collections and cultural heritage",
    "coventry": "Coventry",
    "ee": "Education and employment",
    "equity research": "Equity and representation",
    "genizah": "Manuscripts",
    "hillforts": "Archaeology",
    "khalili": "Collections and cultural heritage",
    "memory of the world": "Collections and cultural heritage",
    "representation": "Equity and representation",
    "screennation": "Film and television",
}
ROOT_DOMAINS = {
    "counting stuff on wikidata": "Wikidata and demographics",
    "voltaire": "Literature",
    "not economics": "Economics",
    "artworks": "Visual arts",
    "art venues": "Visual arts",
    "poems": "Literature",
    "first lines": "Literature",
    "letters": "Literature and publishing",
    "project gutenberg": "Literature and publishing",
    "lifeboat stations": "Maritime",
    "world war i": "First World War",
    "theses": "Universities and research",
    "english wikisource": "Literature and publishing",
    "wikisource maintenance": "Literature and publishing",
    "white rose research online": "Universities and research",
    "doctoral advisor family trees": "Universities and research",
    "scholarly societies": "Universities and research",
    "bodleian libraries collections": "Collections and cultural heritage",
}
FEATURES = {
    "optional": "optional",
    "union": "union",
    "bind": "bind",
    "values": "values",
    "group": "grouped",
    "order": "ordered",
    "limit": "bounded",
    "distinct": "distinct",
    "minus": "minus",
    "exists": "exists",
    "service": "service",
    "filter": "filter",
}


def read_json(path):
    return json.loads(path.read_bytes())


def digest(data):
    return hashlib.sha256(data).hexdigest()


def plain_heading(value):
    value = re.sub(r"\[\[(?:[^|\]]+\|)?([^\]]+)\]\]", r"\1", value)
    return re.sub(r"'{2,5}", "", value).strip()


def source_templates(page):
    """Locate query text and its heading path directly in pinned wikitext."""
    text = page["wikitext"]
    headings = iter(HEADING.finditer(text))
    current = next(headings, None)
    section_path = []
    for match in TEMPLATE.finditer(text):
        while current is not None and current.start() < match.start():
            level = len(current[1])
            section_path = [(depth, title) for depth, title in section_path if depth < level]
            section_path.append((level, plain_heading(current[2])))
            current = next(headings, None)
        yield match[1].upper(), match[2], [title for _, title in section_path], match.start(2)


def assemble_sources():
    """Match the historical records to source bytes, append typo recoveries."""
    pages = read_json(PAGES)["pages"]
    corpus = read_json(CORPUS)
    observed = {}
    recovered = []
    base_rows = corpus["queries"]
    for page in pages:
        if digest(page["wikitext"].encode()) != page["sha256"]:
            raise ValueError(f"Unexpected revision hash for {page['title']}")
        ordinal = 0
        for template, text, path, start in source_templates(page):
            if template == "SPARFQL":
                recovered.append({
                    "page": page["title"],
                    "revision": page["revision"],
                    "revision_url": page["revision_url"],
                    "history_url": page["history_url"],
                    "section": path[-1] if path else None,
                    "ordinal": None,
                    "query": text,
                    "section_path": path,
                    "wikitext_offset": start,
                    "template_kind": template,
                })
                continue
            ordinal += 1
            observed[(page["title"], ordinal)] = (template, text, path, start)
    if len(observed) != len(base_rows):
        raise ValueError("The pinned page snapshot and historical harvest differ in size")
    rows = []
    for row in base_rows:
        template, text, path, start = observed[(row["page"], row["ordinal"])]
        if text != row["query"]:
            raise ValueError(f"Historical query differs from revision snapshot: {row['page']} {row['ordinal']}")
        rows.append({
            **row, "section_path": path, "wikitext_offset": start, "template_kind": template
        })
    return rows + recovered, pages


def prepare(query, language):
    """Expand the wikitext pipe escape and optionally select an explicit language."""
    text = query.replace(WIKI_PIPE, "|")
    if language is not None:
        text = LANGUAGE_PARAM.sub(
            lambda match: match[1] + match[2] + match[3].replace(AUTO_LANGUAGE, language) + match[2],
            text,
        )
    return text


def catalogue_tags(text):
    """Infer a query form and catalogue features from lexical tokens."""
    tokens = [m[0].lower() for m in TOKEN.finditer(text) if not m[0].startswith("#")]
    form = "unknown"
    depth = 0
    for token in tokens:
        if token == "{":
            depth += 1
        elif token == "}":
            depth -= 1
        elif depth == 0 and token in QUERY_FORMS:
            form = token
            break
    words = set(tokens)
    tags = {tag for keyword, tag in FEATURES.items() if keyword in words}
    if words & {"count", "sum", "avg", "sample", "min", "max", "group_concat"}:
        tags.add("aggregation")
    if words & {"wikibase:label", "<http://wikiba.se/ontology#label>"}:
        tags.add("labels")
    if words & {"wdt:p625", "wikibase:around", "wikibase:box"}:
        tags.add("coordinates")
    if words & {"wikibase:around", "wikibase:box", "geof:distance"}:
        tags.add("geo")
    if any(token.startswith("hint:") for token in words):
        tags.add("query hints")
    if AUTO_LANGUAGE in text:
        tags.add("automatic language")
    displays = re.findall(r"(?im)^\s*#\s*defaultView\s*:\s*(\w+)", text)
    tags.update(display.lower() for display in displays)
    return form, sorted(tags)


def query_domain(source):
    path = source["section_path"]
    slug = source["page"].partition("/queries/")[2].lower()
    if slug:
        return SUBPAGE_DOMAINS.get(slug, slug.capitalize())
    major = path[0] if path else "General"
    if major.lower().startswith("university of ") or major == "Universities of the UK":
        return "Universities and research"
    return ROOT_DOMAINS.get(major.lower(), major)


def query_title(source):
    path = source["section_path"]
    if path and len(path[-1]) > 24:
        return path[-1]
    explicit = re.search(r"(?im)^\s*#\s*title\s*:\s*([^\r\n]+)", source["query"])
    if explicit:
        return explicit[1].strip()
    return " · ".join(path[-2:]) if path else source["page"]


def run_java(jar, inputs):
    records = [
        {"protocol_version": 1, "request_id": key, "query_id": key, "query": query}
        for key, query in inputs.items()
    ]
    wire = "".join(json.dumps(record, ensure_ascii=False) + "\n" for record in records)
    result = subprocess.run(
        ["java", "-Xmx512m", "-Xss16m", "-jar", str(jar)],
        input=wire, cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        check=True, timeout=300,
    )
    replies = [json.loads(line) for line in result.stdout.splitlines()]
    if len(replies) != len(records):
        raise ValueError(f"Expected {len(records)} Java responses, got {len(replies)}")
    outputs = {}
    for key, reply in zip(inputs, replies, strict=True):
        if reply.get("status") != "ok" or reply.get("request_id") != key or reply.get("query_id") != key:
            raise ValueError(f"Invalid oracle response to {key}: {reply}")
        if reply.get("query_sha256") != digest(inputs[key].encode()):
            raise ValueError(f"Oracle query hash mismatch for {key}")
        outputs[key] = reply["result"]
    return outputs


def lean_source_hashes():
    sources = ROOT / "formal/lean4/L4Factoidal/Wikidata"
    hashes = {file.name: digest(file.read_bytes()) for file in sorted(sources.glob("*.lean"))}
    hashes["Wikidata/ParseBatch.lean"] = digest((sources.parents[1] / "Wikidata/ParseBatch.lean").read_bytes())
    return hashes


def write_catalogue(path, metadata, rows):
    data = {**metadata, "count": len(rows), "queries": rows}
    path.parent.mkdir(parents=True, exist_ok=True)
    with NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        temp_path = Path(stream.name)
    try:
        temp_path.write_text(
            json.dumps(data, ensure_ascii=False, separators=(",", ":")) + "\n", encoding="utf-8"
        )
        temp_path.replace(path)
    finally:
        temp_path.unlink(missing_ok=True)
    statuses = Counter(row["rewrite_status"] for row in rows)
    print(f"{path}: {len(rows)} queries, statuses {dict(statuses)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jar", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--first-100-out", type=Path)
    parser.add_argument("--with-lean", action="store_true")
    parser.add_argument("--language", default="en")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-zA-Z]{2,8}(?:-[a-zA-Z0-9]{1,8})*", args.language):
        parser.error("--language must be an explicit language tag such as en or pt-br")
    language = args.language.lower()
    jar = args.jar.resolve(strict=True)
    lean_hashes = lean_source_hashes() if args.with_lean else None
    source_rows, pages = assemble_sources()
    sources = {f"mlp-{index:03}": source for index, source in enumerate(source_rows, 1)}
    classic_templates = {key: prepare(source["query"], None) for key, source in sources.items()}
    classic = {key: prepare(source["query"], language) for key, source in sources.items()}
    template_results = run_java(jar, classic_templates)
    results = run_java(jar, classic)
    original_ids = {}
    classic_ids = {}
    replacement_ids = {}
    if args.with_lean:
        def parse_inputs(inputs, prefix):
            return [{"id": prefix + key, "query": query} for key, query in inputs.items()]

        original_ids = {key: source["query"] for key, source in sources.items()}
        classic_ids = {key: text for key, text in classic.items() if text != original_ids[key]}
        replacement_ids = {
            key: result["rewritten_query"] for key, result in results.items()
            if result["rewritten_query"] is not None
        }
        lean = run_lean(
            parse_inputs(original_ids, "source-") + parse_inputs(classic_ids, "classic-")
            + parse_inputs(replacement_ids, "replacement-")
        )
        lean_requests = parse_inputs(classic_templates, "")
        lean_rewrites = run_lean(lean_requests, language)
        lean_templates = run_lean(lean_requests, LEAN_LANGUAGE_MARKER)
    else:
        lean = {}
        lean_rewrites = {}
        lean_templates = {}

    audit = json.loads(Path(__file__).with_name("mlp_audit.json").read_text(encoding="utf-8"))
    rows = []
    for key, source in sources.items():
        text = source["query"]
        form, tags = catalogue_tags(classic_templates[key])
        result = results[key]
        alternate = template_results[key]
        lean_result = lean_rewrites.get(key, {}).get("result", {})
        lean_template = lean_templates.get(key, {}).get("result", {})
        preparation = []
        if WIKI_PIPE in text:
            preparation.append("mediawiki-pipe-escape")
        if classic[key] != classic_templates[key]:
            preparation.append("auto-language")
        row = {
            "id": key,
            "title": query_title(source),
            "domain": query_domain(source),
            "form": form,
            "tags": tags,
            "source": {field: value for field, value in source.items() if field != "query"},
            "original_query": text,
            "classic_query": classic[key],
            "classic_query_template": classic_templates[key],
            "replacement_query": result["rewritten_query"],
            "replacement_query_template": alternate["rewritten_query"],
            "input_preparation": preparation,
            "rewrite_status": result["rewrite_status"],
            "rewrite_rules": result["rewrites"],
            "rewrite_warnings": result["warnings"],
            "rewrite_errors": result["errors"],
            "lean_replacement_query": lean_result.get("rewritten_query"),
            "lean_replacement_query_template": lean_template.get("rewritten_query"),
            "lean_rewrite_status": lean_result.get("rewrite_status"),
            "lean_rewrites": lean_result.get("rewrites", []),
            "lean_rewrite_warnings": lean_result.get("warnings", []),
            "lean_rewrite_errors": lean_result.get("errors", []),
            "lean_parse_accepted": lean.get("source-" + key, {}).get("accepted"),
            "lean_classic_parse": lean.get(("classic-" if key in classic_ids else "source-") + key),
            "lean_replacement_parse": lean.get("replacement-" + key),
        }
        observation = audit.get(key)
        if observation and observation["source_sha256"] == digest(text.encode()):
            review = observation.copy()
            for key in ("replacement_query", "lean_replacement_query"):
                expected = review.pop(key + "_sha256", None)
                actual = row[key]
                if expected and (actual is None or digest(actual.encode()) != expected):
                    review.pop("normalized_rewrite_match", None)
            if len(review) > 1:
                row["review"] = review
        rows.append(row)
    metadata = {
        "schema_version": 1,
        "language": language,
        "license": "CC-BY-SA-4.0",
        "license_url": "https://creativecommons.org/licenses/by-sa/4.0/",
        "attribution": "Martin Poulter and Wikidata contributors",
        "corpus_sha256": digest(CORPUS.read_bytes()),
        "page_snapshot_sha256": digest(PAGES.read_bytes()),
        "source_pages": [
            {field: page[field] for field in ("title", "revision", "timestamp", "revision_url", "history_url", "sha256")}
            for page in pages
        ],
        "rewrite_engine": {
            "name": "Wikimedia original Java rewriter",
            "repository": "https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter",
            "jar_sha256": digest(jar.read_bytes()),
        },
        "lean_language_marker": LEAN_LANGUAGE_MARKER if args.with_lean else None,
        "lean_source_sha256": lean_hashes,
        "extraction": (
            "Every SPARQL/SPARQL2 query template in the 15 pinned pages and a recovered SPARFQL typo. "
            "IDs 1–579 retain historical order. ID 580 is the recovered template."
        ),
        "metadata_method": "Domain from source headings; query form and features inferred from lexical tokens.",
    }
    if args.with_lean and lean_hashes != lean_source_hashes():
        raise ValueError("Lean rewrite sources changed during catalogue generation; rebuild and retry")
    write_catalogue(args.out, metadata, rows)
    if args.first_100_out:
        write_catalogue(args.first_100_out, {**metadata, "sample": "First 100 historical records"}, rows[:100])


if __name__ == "__main__":
    main()
