#!/usr/bin/env python3
"""Compare paired rewrites as bytes, SPARQL tokens and Jena-normalised tokens."""

import argparse
import json
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def run_jsonl(command, records=None, cwd=ROOT):
    request = None if records is None else "".join(json.dumps(row) + "\n" for row in records)
    output = subprocess.run(
        command, input=request, cwd=cwd, capture_output=True, text=True, check=True, timeout=180
    ).stdout
    return {row["id"]: row for row in map(json.loads, output.splitlines())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("catalogue", type=Path)
    parser.add_argument("--jar", type=Path, required=True)
    parser.add_argument("--ecj", type=Path, help="Use this Eclipse compiler JAR if javac is absent")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    archive = args.jar.resolve()
    rows = json.loads(args.catalogue.read_text(encoding="utf-8"))["queries"]
    pairs = [row for row in rows
             if row["rewrite_status"] == row["lean_rewrite_status"] == "rewritten"]
    sides = ("replacement_query", "lean_replacement_query")
    requests = [
        {"id": f"{row['id']}:{side}", "query": row[side]}
        for row in pairs for side in sides
    ]
    requests.extend(
        {"id": f"{row['id']}:original", "query": row["classic_query"], "wdqs_defaults": True}
        for row in rows if row["rewrite_status"] == "parse_error"
    )
    with tempfile.TemporaryDirectory() as temp_dir:
        temp = Path(temp_dir)
        compiler = (["java", "-jar", str(args.ecj.resolve()), "-17", "-proc:none"]
                    if args.ecj else ["javac"])
        subprocess.run(compiler + ["-cp", str(archive), "-d", str(temp),
                                   "tools/wikidata/NormalizeJena.java"], cwd=ROOT, check=True)
        jena = run_jsonl(["java", "-cp", f"{temp}:{archive}",
                          "io.github.andreawesterinen.wikidata.rewriter.NormalizeJena"], requests)
        if set(jena) != {request["id"] for request in requests}:
            raise ValueError("Jena did not return the expected records")
        cases = []
        for row in pairs:
            ident = row["id"]
            source = row["classic_query"]
            a, b = (row[k] for k in sides)
            cases.append({"id": f"{ident}:raw", "source": source, "left": a, "right": b})
            left, right = (jena[f"{ident}:{side}"].get("text") for side in sides)
            if left is not None and right is not None:
                cases.append({"id": f"{ident}:jena", "source": source, "left": left, "right": right})
        path = temp / "queries.json"
        path.write_text(json.dumps(cases), encoding="utf-8")
        tokens = run_jsonl(["lake", "env", "lean", "--run", "Wikidata/NormalizeBatch.lean",
                            str(path)], cwd=ROOT / "formal/lean4")
        if set(tokens) != {case["id"] for case in cases}:
            raise ValueError("Lean did not return the expected token comparisons")
    report = []
    for row in pairs:
        ident = row["id"]
        report.append({
            "id": ident,
            "byte_identical": row[sides[0]] == row[sides[1]],
            "raw_tokens": tokens.get(f"{ident}:raw"),
            "jena_tokens": tokens.get(f"{ident}:jena"),
            "jena_errors": {side: jena[f"{ident}:{side}"].get("error") for side in sides},
        })
    args.out.write_text(json.dumps({
        "paired_rewrites": report,
        "jena_original_rejections": {key: result.get("error") for key, result in jena.items()
                                     if key.endswith(":original")},
    }, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"{len(report)} paired rewrites. "
          f"{sum((row['jena_tokens'] or {}).get('alpha_equal', False) for row in report)} "
          "match after Jena normalisation and generated-variable renaming.")


if __name__ == "__main__":
    main()
