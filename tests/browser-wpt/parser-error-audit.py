#!/usr/bin/env python3
"""Classify raw Lean parser diagnostics without changing the mismatch score.

Input is Harness.Html5lib error-counts JSONL over the pinned document fixtures.
Buckets flag evidence for review; they are not test exclusions or verdicts.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re


def bucket(row):
    if row['expectedCount'] == 0 and row['file'] == 'processing-instructions.dat':
        return 'processing_instructions_empty_expectations'
    if row['hasNewErrors']:
        return 'legacy_and_new_error_sections'
    if row['expectedCount'] == 0:
        return 'other_empty_expectations'
    descriptions = row['expectedDescriptions']
    if (any(re.search(r'\(\d+,\d+\)', value) for value in descriptions)
            and any(re.search(r'\(\d+:\d+\)', value) for value in descriptions)):
        return 'mixed_legacy_and_modern_positions'
    return 'algorithm_review'


def audit(path):
    rows = [json.loads(line) for line in path.read_text().splitlines() if line]
    identities = {(row['file'], row['line'], row['scripting']) for row in rows}
    if len(identities) != len(rows):
        raise ValueError('Duplicate fixture identities in diagnostic log')
    for row in rows:
        if row['expectedCount'] != len(row['expectedDescriptions']):
            raise ValueError('Expected count does not match original descriptions')
        if row['actualCount'] != len(row['treeBuilderErrors']) + len(row['tokenizerErrors']):
            raise ValueError('Actual count does not match emitted diagnostics')
    different = [dict(row, bucket=bucket(row), delta=row['actualCount'] - row['expectedCount'])
                 for row in rows if row['expectedCount'] != row['actualCount']]
    return {
        'format': 'factoidal-html-error-count-audit-v1',
        'scope': 'Document fixtures only; original summed counts; categories do not change scores',
        'sourceSha256': hashlib.sha256(path.read_bytes()).hexdigest(),
        'runnerSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'summary': {
            'documents': len(rows), 'equal': len(rows) - len(different), 'different': len(different),
            'differentWithCorrectTree': sum(row['treeMatches'] for row in different),
            'differentWithIncorrectTree': sum(not row['treeMatches'] for row in different),
            'undercounts': sum(row['delta'] < 0 for row in different),
            'overcounts': sum(row['delta'] > 0 for row in different),
            'deltaRange': [min((row['delta'] for row in different), default=0),
                           max((row['delta'] for row in different), default=0)],
            'buckets': dict(sorted(Counter(row['bucket'] for row in different).items())),
            'files': dict(sorted(Counter(row['file'] for row in different).items())),
        },
        'mismatches': different,
    }


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('jsonl', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    report = audit(args.jsonl)
    # A fresh file prevents an earlier measurement from being overwritten.
    with args.output.open('x') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps(report['summary'], sort_keys=True))
