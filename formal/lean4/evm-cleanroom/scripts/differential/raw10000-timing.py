"""Paired native process timings, one complete raw 10K corpus per sample."""
import hashlib
import json
import math
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

before_path, before_source, after_path, after_source, tsv_path, corpus_path = sys.argv[1:]
pairs = 11
warmup_pairs = 3
path = Path(tsv_path).resolve()
inputs = path.read_bytes()
corpus = Path(corpus_path).read_bytes()
assert len(inputs.splitlines()) == len(corpus.splitlines()) == 10_000
assert hashlib.sha256(inputs).hexdigest() == 'aa2533e3fa8b1d2907e5c84933956e207a53e2b0a674e1d8bef716b1afc99ea0'
assert hashlib.sha256(corpus).hexdigest() == '610012bd5b278c5e4d08545560beed11910e01c0233ad8f9c9a4c9a52e0a2efb'

engines = {}
for lane, program, source in [
    ('before', before_path, before_source), ('after', after_path, after_source),
]:
    executable = Path(program).resolve()
    engines[lane] = {
        'executable': str(executable), 'source': source,
        'sha256': hashlib.sha256(executable.read_bytes()).hexdigest(),
    }
assert engines['before']['sha256'] != engines['after']['sha256']

expected = None
samples = []
for pair in range(-warmup_pairs, pairs):
    order = ['before', 'after'] if pair % 2 == 0 else ['after', 'before']
    sample = {'first': order[0]}
    for lane in order:
        start = time.perf_counter_ns()
        proc = subprocess.run(
            [engines[lane]['executable'], '--batch', str(path)],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30, check=True,
        )
        sample[lane] = time.perf_counter_ns() - start
        assert not proc.stderr, proc.stderr
        if expected is None:
            expected = proc.stdout
            assert len(expected.splitlines()) == 10_000
        assert proc.stdout == expected, f'raw batch output changed in {lane}'
    if pair >= 0:
        samples.append(sample)

def stats(times):
    values = sorted(times)
    return {
        **{f'p{int(q * 100)}': values[math.ceil(q * len(values)) - 1] for q in (0.50, 0.95, 0.99)},
        'min': values[0], 'max': values[-1], 'spread': values[-1] - values[0]
    }

print(json.dumps({
    'kind': 'paired-native-raw-evm-batch-timing',
    'units': 'nanoseconds per 10000-case batch',
    'quantiles': 'nearest rank',
    'measured': 'child process launch, TSV read, interpretation, JSONL serialization and process exit',
    'system': {'platform': platform.platform(), 'logicalCpus': os.cpu_count(), 'python': platform.python_version()},
    'date': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
    'engines': engines, 'casesPerSample': 10_000, 'measuredPairs': pairs, 'warmupPairs': warmup_pairs,
    'inputSha256': hashlib.sha256(inputs).hexdigest(), 'corpusSha256': hashlib.sha256(corpus).hexdigest(),
    'outputBytes': len(expected), 'outputSha256': hashlib.sha256(expected).hexdigest(), 'outputsByteIdentical': True,
    'samples': samples,
    'before': stats([sample['before'] for sample in samples]),
    'after': stats([sample['after'] for sample in samples]),
    'pairedAfterMinusBefore': stats([sample['after'] - sample['before'] for sample in samples]),
}, separators=(',', ':')))
