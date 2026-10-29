#!/usr/bin/env bash
# The Notation3 reader on the W3C N3 Community Group suite and on the Turtle
# suites (https://github.com/danbri/factoidal/issues/1171).
#
#   tests/n3/run.sh            build `l4n3`, run every manifest below
#
# Each line runs `lake exe l4n3` on one manifest. The run fails when a counted
# test fails (rdft:Rejected entries are counted apart and do not fail it) or
# when the N3 and Turtle readers disagree on a Turtle test (`turtle-agreement`).
# Suites: third_party/testing/n3 (pinned, third_party/testing/n3-PROVENANCE.md)
# and third_party/testing/w3c (RDF 1.1 and RDF 1.2 Turtle).
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LEAN="${ROOT}/formal/lean4"
N3="${ROOT}/third_party/testing/n3/tests"
W3C="${ROOT}/third_party/testing/w3c/rdf"

for f in "${N3}/N3Tests/manifest-parser.ttl" "${W3C}/rdf11/rdf-turtle/manifest.ttl"; do
  if [ ! -f "$f" ]; then
    echo "missing suite file: $f (run: git submodule update --init third_party/testing/n3 third_party/testing/w3c)" >&2
    exit 2
  fi
done

(cd "${LEAN}" && lake build l4n3) || exit 2
BIN="${LEAN}/.lake/build/bin/l4n3"

status=0
run() {
  local rc=0
  timeout 600 "${BIN}" --quiet "$@" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAILED (exit ${rc}): l4n3 $*"
    status=1
  fi
}

run "${N3}/N3Tests/manifest-parser.ttl"
run "${N3}/N3Tests/manifest-extended.ttl"
run "${N3}/N3Tests/manifest-reasoner.ttl"
run "${N3}/TurtleTests/manifest.ttl"
run "${W3C}/rdf11/rdf-turtle/manifest.ttl"
run --rdf12 "${W3C}/rdf12/rdf-turtle/syntax/manifest.ttl"
run --rdf12 "${W3C}/rdf12/rdf-turtle/eval/manifest.ttl"

# Stack cases (Lean tail-recursion rule, CLAUDE.md): each sequence of the
# grammar 200,000 long, read, written, read again, compared, converted to RDF
# and checked against the Turtle reader, and, for the reasoner, a rule body of
# 20,000 triples, a list pattern of 200,000 members and a graph-term pattern of
# 2,000 triples, with a 512 KB stack. The depth of the
# N3 functions follows the nesting of a document only
# (tools/lean-tail-recursion-allow.txt, the N3 lines).
STACK="$(mktemp -d "${TMPDIR:-/tmp}/n3-stack-XXXXXX")"
trap 'rm -rf "${STACK}"' EXIT
python3 - "${STACK}" <<'PY'
import sys, os
d = sys.argv[1]; n = 200000
docs = {
  'formula': ':a :b {\n' + ''.join(f':s{i} :p :o .\n' for i in range(n)) + '} .\n',
  'list': ':a :b (' + ' '.join(f':x{i}' for i in range(n)) + ') .\n',
  'pol': ':a ' + ' ;\n'.join(f':p{i} :o' for i in range(n)) + ' .\n',
  'objs': ':a :p ' + ', '.join(f':o{i}' for i in range(n)) + ' .\n',
  'path': ':a' + ''.join(f'!:p{i}' for i in range(n)) + ' :q :r .\n',
  'doc': ''.join(f':s{i} :p _:b{i} .\n' for i in range(n)),
}
entries = []
for k, body in docs.items():
  text = '@prefix : <http://ex/> .\n' + body
  for suffix in ('', '-r'):
    open(os.path.join(d, k + suffix + '.n3'), 'w').write(text)
  entries.append(f'<#{k}e> a test:TestN3Eval ; mf:name "{k}-eval" ; mf:action <{k}.n3> ; mf:result <{k}-r.n3> .\n'
                 f'<#{k}s> a test:TestN3PositiveSyntax ; mf:name "{k}-syntax" ; mf:action <{k}.n3> .\n'
                 f'<#{k}t> a rdft:TestTurtlePositiveSyntax ; mf:name "{k}-turtle" ; mf:action <{k}.n3> .\n')
names = ' '.join(f'<#{k}e> <#{k}s> <#{k}t>' for k in docs)
# The reasoner: one rule whose body has 20,000 triples, all in the data.
m = 20000
open(os.path.join(d, 'rbody.n3'), 'w').write('@prefix : <http://ex/> .\n' +
  ''.join(f':s{i} :p :o{i} .\n' for i in range(m)) +
  '{ ' + ' '.join(f':s{i} :p ?x{i} .' for i in range(m)) + ' } => { :done a :Ok } .\n')
open(os.path.join(d, 'rbody-r.n3'), 'w').write('@prefix : <http://ex/> .\n:done a :Ok .\n')
names += ' <#rbody> <#rlist> <#rgraph>'
# A list pattern of 200,000 members, and a graph-term pattern of 2,000 triples.
lst = '(' + ' '.join(str(i) for i in range(n)) + ')'
open(os.path.join(d, 'rlist.n3'), 'w').write('@prefix : <http://ex/> .\n:a :p ' + lst + ' .\n'
  '{ :a :p ' + lst + ' } => { :done a :Ok } .\n')
gt = '{ ' + ' '.join(f':s{i} :p :o{i} .' for i in range(2000)) + ' }'
open(os.path.join(d, 'rgraph.n3'), 'w').write('@prefix : <http://ex/> .\n:g :is ' + gt + ' .\n'
  '{ :g :is ' + gt + ' } => { :done a :Ok } .\n')
for k in ('rlist', 'rgraph'):
  entries.append(f'<#{k}> a test:TestN3Reason ; mf:name "{k}" ; mf:action <{k}.n3> ; '
                 'mf:result <rbody-r.n3> ; test:options [ test:think true ; test:conclusions true ] .\n')
entries.append('<#rbody> a test:TestN3Reason ; mf:name "rule-body-20000" ; mf:action <rbody.n3> ; '
               'mf:result <rbody-r.n3> ; test:options [ test:think true ; test:conclusions true ] .\n')
open(os.path.join(d, 'manifest.ttl'), 'w').write(
  '@prefix mf: <http://www.w3.org/2001/sw/DataAccess/tests/test-manifest#> .\n'
  '@prefix test: <https://w3c.github.io/N3/tests/test.n3#> .\n'
  '@prefix rdft: <http://www.w3.org/ns/rdftest#> .\n'
  f'<> mf:entries ( {names} ) .\n' + ''.join(entries))
PY
rc=0
( ulimit -s 512; timeout 900 "${BIN}" --quiet "${STACK}/manifest.ttl" ) || rc=$?
if [ "$rc" -ne 0 ]; then
  echo "FAILED (exit ${rc}): stack cases with a 512 KB stack"
  status=1
fi

exit "${status}"
