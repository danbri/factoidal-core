#!/usr/bin/env python3
"""Check actual Lean #print axioms output against the pinned active ledger.

Unlike a textual check for the presence of '#print axioms', this invokes the
version-pinned Lean toolchain for each selected source file. It fails closed if
Lean cannot elaborate, a named theorem has no actual printed axiom list, or
its exact list differs from the manifest (including a newly introduced axiom).

This is a selected-theorem audit, NOT a proof of Ethereum refinement, nor a
substitute for the compiler/kernel and axiom-audit trust boundary.
"""
import argparse
import json
from collections import defaultdict
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'evidence/active-claim-manifest-v2.json'
PRINTED = re.compile(
    r"'(?P<name>EVMCleanroom\.[^']+)' "
    r"(?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|(?P<none>does not depend on any axioms))"
)
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}


def require(condition, explanation):
    if not condition:
        raise ValueError(explanation)


def extract_printed(text):
    """Return all actual theorem/axiom messages in an elaborator transcript."""
    found = defaultdict(list)
    # Lean wraps long axiom lists across lines when invoked directly. Match
    # complete reports, retaining every axiom and duplicate theorem report.
    for match in PRINTED.finditer(text):
        raw = match.group('axioms')
        axioms = tuple(sorted(a.strip() for a in raw.split(',') if a.strip())) if raw else ()
        require(len(set(axioms)) == len(axioms), 'duplicate printed axiom')
        found[match.group('name')].append(axioms)
    return found


def verify_printed(expected, printed):
    """Demand exact matching sets; missing, duplicated or extra axioms fail."""
    for claim in expected:
        name = claim['name']
        declared = claim['axioms_printed']
        require(isinstance(declared, list) and len(set(declared)) == len(declared),
                'bad declared axiom list: ' + name)
        require(set(declared).issubset(ALLOWED), 'untrusted claimed axiom: ' + name)
        seen = printed.get(name, [])
        require(len(seen) == 1, 'missing or ambiguous actual #print axioms: ' + name)
        require(set(seen[0]) == set(declared),
                'AXIOM DRIFT: ' + name + ' claimed=' + str(declared) +
                ' actual=' + str(seen[0]))
    return len(expected)


def selftest():
    sample = "info: x.lean:9:0: 'EVMCleanroom.Demo.someTheorem' depends on axioms: [propext, Quot.sound]"
    no_axioms = "info: x.lean:10:0: 'EVMCleanroom.Demo.trivial' does not depend on any axioms"
    emitted = extract_printed(sample + '\n' + no_axioms)
    good = [
        {'name': 'EVMCleanroom.Demo.someTheorem', 'axioms_printed': ['propext', 'Quot.sound']},
        {'name': 'EVMCleanroom.Demo.trivial', 'axioms_printed': []},
    ]
    require(verify_printed(good, emitted) == 2, 'valid test rejected')
    wrapped = sample.replace('[propext, Quot.sound]', '[propext,\n Quot.sound]')
    require(verify_printed(good, extract_printed(wrapped + '\n' + no_axioms)) == 2,
            'valid wrapped theorem output rejected')
    corrupt = [
        [dict(good[0], axioms_printed=['propext']), good[1]],
        [dict(good[0], axioms_printed=['propext', 'sorryAx']), good[1]],
        [good[0], dict(good[1], name='EVMCleanroom.Demo.missing')],
    ]
    rejected = 0
    for forged in corrupt:
        try:
            verify_printed(forged, emitted)
        except ValueError:
            rejected += 1
    corrupt_transcripts = [
        wrapped.replace('Quot.sound]', 'sorryAx,\n Quot.sound]') + '\n' + no_axioms,
        wrapped + '\n' + wrapped + '\n' + no_axioms,
    ]
    for forged in corrupt_transcripts:
        try:
            verify_printed(good, extract_printed(forged))
        except ValueError:
            rejected += 1
    require(rejected == len(corrupt) + len(corrupt_transcripts),
            'adversarial control not rejected')
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    if args.selftest:
        print(json.dumps({'status': 'negative-controls-pass', 'rejected': selftest()}))
        return
    manifest = json.loads(MANIFEST.read_text())
    claims = manifest['theorem_inventory']
    require(len(claims) >= 10, 'unexpected theorem inventory length')
    grouped = defaultdict(list)
    for claim in claims:
        source = claim['source']
        require(source in manifest['source_blobs'], 'unpinned source: ' + source)
        grouped[source].append(claim)
    for source, assertions in grouped.items():
        require((ROOT / source).is_file(), 'missing theorem source: ' + source)
        result = subprocess.run(
            ['lake', '-d', 'evm-cleanroom', 'env', 'lean', str(ROOT / source)], cwd=ROOT.parent,
            text=True, capture_output=True, timeout=120, check=False,
        )
        require(result.returncode == 0,
                'Lean failed to elaborate ' + source + ': ' +
                (result.stdout + result.stderr)[-2500:])
        actual = extract_printed(result.stdout + '\n' + result.stderr)
        verify_printed(assertions, actual)
    print(json.dumps({
        'status': 'printed-axioms-match-manifest',
        'selectedTheorems': len(claims), 'sourceFiles': len(grouped),
        'allowedAxioms': sorted(ALLOWED),
    }))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError,
            subprocess.TimeoutExpired, json.JSONDecodeError) as exc:
        print('active theorem axiom output check failed:', exc, file=sys.stderr)
        sys.exit(1)
