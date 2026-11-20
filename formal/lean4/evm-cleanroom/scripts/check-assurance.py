#!/usr/bin/env python3
"""Check the scoped evidence snapshot and optionally a fresh replay result.

This checks consistency, not the truth of Lean propositions or Ethereum semantics.
"""
import argparse
import collections
import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise ValueError(message)

def check_result(result, replay):
    # This is a frozen evidence snapshot. A new replay is checked against
    # *every observable recorded in the committed, SHA-pinned reference*, not
    # just the four final roots. Otherwise a regression in fee accounting,
    # log hashes, or provenance could silently retain a green badge.
    snapshot_path = ROOT / replay['result_snapshot']
    require(digest(snapshot_path) == replay['result_sha256'],
            'reference snapshot hash mismatch')
    baseline = json.loads(snapshot_path.read_text())
    require(set(result) == set(baseline), 'result schema fields changed')
    require(result['schemaVersion'] == baseline['schemaVersion'],
            'result schema version changed')
    require(result['kind'] == baseline['kind'], 'result kind changed')
    require(result['provenance'] == baseline['provenance'],
            'replay provenance changed')
    require(result['limits'] == baseline['limits'],
            'declared observation/trust limits changed')
    counts = replay['counts']
    require(result['provenance']['sha256'] == replay['fixture_sha256'], 'fixture hash mismatch')
    require(result['provenance']['totalFixtureCases'] == counts['total'], 'fixture total mismatch')
    require(result['status'] == 'pass', 'replay status is not pass')
    for key in ('passed', 'failed', 'unsupported'):
        require(result[key] == counts[key], f'{key} count changed')
    require(result['actualLeanStateTestsExecuted'] == counts['executed'] == counts['passed'] + counts['failed'], 'executed count mismatch')
    cases = result['cases']
    require(len(cases) == counts['total'], 'case list length mismatch')
    require(len({c['id'] for c in cases}) == len(cases), 'duplicate case ID')
    statuses = collections.Counter(c['status'] for c in cases)
    require(statuses == collections.Counter({'pass': counts['passed'], 'unsupported': counts['unsupported']}), 'case status counts differ')
    expected = {c['id']: c for c in replay['cases']}
    require(len(expected) == counts['total'] and set(expected) == {c['id'] for c in cases}, 'case inventory changed')
    for case in cases:
        old = expected[case['id']]
        require(case['status'] == old['status'], 'case classification changed: '+case['id'])
        reference = next(c for c in baseline['cases'] if c['id'] == case['id'])
        changed = sorted(k for k in set(case) | set(reference)
                         if case.get(k) != reference.get(k))
        require(not changed, 'case observable changed: '+case['id']+
                ' fields='+','.join(changed))
        if case['status'] == 'pass':
            require(case.get('expectedStateRoot') == old['expected_state_root'] == case.get('computedStateRoot'), 'state root changed: '+case['id'])
        else:
            require(case.get('reason') == old['reason'], 'unsupported reason changed: '+case['id'])

def check_fixture(fixture, replay):
    """Verify reported test-source provenance in the actual pinned bytes.

    This checks fixture metadata and expected hashes, not the provenance
    of the filling-tool binary or its faithful implementation of EELS.
    """
    source = replay['upstream_test_source']
    expected = {c['id']: c for c in replay['cases']}
    require(isinstance(fixture, dict) and set(fixture) == set(expected),
            'fixture case inventory differs from manifest')
    for case_id, record in fixture.items():
        info = record.get('_info', {})
        expected_url = (source['test_source_repository'] + '/blob/' +
                        source['fixture_reported_tag'] + '/' +
                        source['source_path'])
        require(str(info.get('url', '')).split('#')[0] == expected_url,
                'fixture test source differs: ' + case_id)
        require(info.get('filling-transition-tool') ==
                source['filling_transition_tool'], 'fixture filling tool differs: ' + case_id)
        require(info.get('reference-spec-version') ==
                source['reference_spec_version'], 'fixture reference EIP changed: ' + case_id)
        require(info.get('fixture-format') == 'state_test',
                'fixture format changed: ' + case_id)
        post = record.get('post', {}).get(replay['fork'], [])
        require(len(post) == 1, 'fixture Prague vector count changed: ' + case_id)
        require(post[0].get('hash') is not None,
                'fixture missing expected root: ' + case_id)
        if expected[case_id]['status'] == 'pass':
            require(post[0]['hash'] == expected[case_id]['expected_state_root'],
                    'fixture expected root differs: ' + case_id)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--result', type=pathlib.Path, help='also compare a fresh runner result')
    parser.add_argument('--fixture', type=pathlib.Path,
                        help='also verify downloaded EELS fixture bytes and _info metadata')
    args = parser.parse_args()
    manifest = json.loads((ROOT/'evidence/claim-manifest-v1.json').read_text())
    require(manifest['schema_version'] == 1, 'unsupported manifest schema')
    replay = manifest['replay']
    for path, expected in [(replay['result_snapshot'], replay['result_sha256']), (replay['dependency_lock'], replay['dependency_lock_sha256'])]:
        require(digest(ROOT/path) == expected, 'hash mismatch: '+path)
    for claim in manifest['theorems']:
        require(digest(ROOT/claim['source_path']) == claim.get('current_source_sha256', claim['source_sha256']), 'theorem source changed: '+claim['source_path'])
    check_result(json.loads((ROOT/replay['result_snapshot']).read_text()), replay)
    if args.result:
        check_result(json.loads(args.result.read_text()), replay)
    if args.fixture:
        raw_fixture = args.fixture.read_bytes()
        require(hashlib.sha256(raw_fixture).hexdigest() == replay['fixture_sha256'],
                'downloaded fixture bytes do not match pinned SHA-256')
        check_fixture(json.loads(raw_fixture), replay)
    counts = replay['counts']
    text = (ROOT/'SOUNDNESS.md').read_text()
    expected = f"Replay snapshot: {counts['passed']} passed, {counts['failed']} failed, {counts['unsupported']} unsupported, {counts['total']} total."
    require(expected in text, 'SOUNDNESS replay summary does not match manifest')
    require('zero official state-test passes claimed' not in text, 'obsolete global zero-passes claim')
    print('assurance snapshot consistent' +
          ('; fresh replay matches' if args.result else '') +
          ('; EELS fixture metadata verified' if args.fixture else ''))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print('assurance check failed:', exc, file=sys.stderr)
        sys.exit(1)
