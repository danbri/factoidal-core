#!/usr/bin/env python3
"""Generate and admit a bounded synthetic corpus through native Lean storage.

Preparation is separate from benchmark query timings. Existing directories
are refused; only processes started by this invocation are stopped.
"""
import argparse
from datetime import datetime, timezone
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

SPEC = importlib.util.spec_from_file_location("snapshot_bench", Path(__file__).with_name(
    "blockengine-snapshot-session-bench.py"))
B = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(B)
D = B.D


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--corpus', choices=['scale', 'relational'], required=True)
    parser.add_argument('--subjects', type=D.bounded_number(10, 300000), required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--timeout', type=D.bounded_number(1, 600, False), default=120)
    parser.add_argument('--collection-max-files', type=D.bounded_number(128, 4096), default=1024)
    args = parser.parse_args()
    directory = args.output_dir.resolve()
    if directory.exists() and any(directory.iterdir()):
        parser.error('output directory must be absent or empty')
    corpus = D.load_corpus(args.corpus)
    binaries = {name: D.BIN / name for name in
                ('l4block-shard-pack', 'l4block-shard-activate', 'l4block-snapshot-session')}
    if any(not binary.is_file() for binary in binaries.values()):
        parser.error('native pack, activate and snapshot binaries must already exist')
    directory.mkdir(parents=True, exist_ok=True)
    report = {'all_checks_passed': False, 'scope': 'native fixture preparation and admission; no query latency claim',
              'timestamp_utc': datetime.now(timezone.utc).isoformat(), 'corpus': args.corpus,
              'subjects': args.subjects, 'triples': corpus.triple_count(args.subjects),
              'driver_sha256': D.sha256(Path(__file__)), 'corpus_sha256': D.sha256(corpus.source_file),
              'collection_limits': {'max_bytes': 512 * 1024 * 1024, 'max_files': args.collection_max_files},
              'binary_sha256': {name: D.sha256(binary) for name, binary in binaries.items()}, 'steps': []}
    session = None
    try:
        fixture = directory / 'fixture.ttl'
        fixture.write_bytes(corpus.fixture_bytes(args.subjects))
        report['fixture_bytes'] = fixture.stat().st_size
        report['fixture_sha256'] = D.sha256(fixture)
        if report['fixture_bytes'] > 256 * 1024 * 1024:
            raise ValueError('fixture exceeds 256 MiB')
        collection = directory / 'collection'
        budget = D.Budget(4 * 1024 * 1024, time.monotonic() + 3 * args.timeout)
        for name, arguments in [
            ('l4block-shard-pack', [fixture, collection / 'first', 'ibk3']),
            ('l4block-shard-activate', [collection, 'first']),
        ]:
            print(f'start corpus={args.corpus} subjects={args.subjects} {name}', file=sys.stderr, flush=True)
            step = D.capture(list(map(str, [binaries[name], *arguments])), directory, name,
                             args.timeout, 2 * 1024 * 1024, budget)
            report['steps'].append(step)
            if step['exit_code'] or step['failure']:
                raise ValueError(f'{name} failed; see retained output')
        report['collection_sha256'] = D.collection_hashes(collection, **report['collection_limits'])
        started = time.perf_counter_ns()
        session = B.Process([binaries['l4block-snapshot-session'], collection], directory / 'snapshot.stderr', args.timeout)
        ready = json.loads(session.line(), object_pairs_hook=D.unique_keys, parse_constant=D.reject_constant)
        report['admission_wall_ns'] = time.perf_counter_ns() - started
        report['ready'] = ready
        if (ready.get('ready'), ready.get('triples')) != (True, corpus.triple_count(args.subjects)):
            raise ValueError('admitted graph cardinality differs from corpus')
        if any(D.sha256(binary) != report['binary_sha256'][name] for name, binary in binaries.items()):
            raise ValueError('binary changed during preparation')
        report['all_checks_passed'] = True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        report['error'] = str(error)
    finally:
        if session:
            try:
                session.close()
            except (OSError, ValueError, subprocess.SubprocessError) as error:
                report['all_checks_passed'] = False
                report['shutdown_error'] = str(error)
        (directory / 'preparation.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(f'report={directory / "preparation.json"} all_checks_passed={report["all_checks_passed"]}')
    return 0 if report['all_checks_passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
