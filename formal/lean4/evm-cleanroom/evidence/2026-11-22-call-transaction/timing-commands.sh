#!/usr/bin/env bash
set -euo pipefail

workspace=/workspace/scratch/144b70d8ac20
evm_source="$workspace/factoidal-core/formal/lean4/evm-cleanroom"
output="$workspace/contract-phase-results/final-phase-timing"
before="$workspace/contract-phase-results/baseline-254c8329-evm-subset"
after="$evm_source/.lake/build/bin/evm-subset"
before_local=254c8329a8cd7da95b51901ba2091fa3ce43a97e
before_public_equivalent=d3843c42d3b9c6fea8e96c3d0eebd65890dbea4b
after_local=ff345ca6e922fb2e96394de436804bee6c5b7f77
tsv="$workspace/baseline-diff.json.lean-input.tsv"
corpus="$workspace/baseline-corpus.jsonl"

verify_binaries() {
  printf '%s  %s\n%s  %s\n' \
    64a6f3a563bdec24a7516d5a2a6698891ee193efa843ed68bb9e838fca6aad77 "$before" \
    3cf7b69691bab210360d8766fc58a9c6cc8d0a133060ab46707051437e6205e5 "$after" |
    sha256sum --check
}

run() {
  verify_binaries
  printf 'Baseline local source %s; public source equivalent %s\n' "$before_local" "$before_public_equivalent"
  printf 'Candidate local runtime source %s\n' "$after_local"
  printf 'Repository head at start: '
  git -C "$workspace/factoidal-core" rev-parse HEAD
  printf 'Candidate local source tree: '; git -C "$workspace/factoidal-core" rev-parse "$after_local^{tree}"
  date -u '+Measurement started %Y-%m-%dT%H:%M:%SZ'
  uname -a
  cat /proc/loadavg
  cat /sys/fs/cgroup/cpu.max /sys/fs/cgroup/cpuset.cpus.effective 2>/dev/null || true
  node --version
  python3 --version
  sha256sum "$tsv" "$corpus" "$evm_source/scripts/differential/byte-call-timing.mjs" "$evm_source/scripts/differential/raw10000-timing.py"

  node "$evm_source/scripts/differential/byte-call-timing.mjs" \
    "$before" "$before_local" "$after" "$after_local" > "$output.legacy-cli.json"
  python3 "$evm_source/scripts/differential/raw10000-timing.py" \
    "$before" "$before_local" "$after" "$after_local" "$tsv" "$corpus" > "$output.raw10000.json"

  date -u '+Measurement finished %Y-%m-%dT%H:%M:%SZ'
  cat /proc/loadavg
  verify_binaries
}

if [[ ${1:-} == locked ]]; then
  run > "$output.environment.log" 2> "$output.stderr.log"
else
  exec flock -w 45 /tmp/foafnaut-timing.lock bash "$0" locked
fi
