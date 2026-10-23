#!/usr/bin/env bash
#
# tests/sbm11/run.sh — SBM11 stage 4, SPARQL over a generation
# (https://github.com/danbri/factoidal/issues/790), and stage 5, the delta
# overlay and compaction (https://github.com/danbri/factoidal/issues/791; tracking
# https://github.com/danbri/factoidal/issues/787). Record:
# docs/designissues/2026-10-12-sbm11-stage4.md.
#
#   (a) oracle   q01 to q21 (tests/qlvr/queries) through `l4sbm11 query` on
#                the olympics generation against the QLever oracle
#                (QLVR_WORK/oracle/*.srj), as multisets by value, with the
#                differences of the comparison record section 3.3 handled as
#                that section says (tests/sbm11/compare_oracle.py). Prints
#                "N pass, M fail (out of 21)".
#   (b) render   every oracle query answered twice, by the key printer (the
#                default) and with --reference-render (every term through
#                jsonOfTerm); the outputs must be byte-identical.
#   (c) ids vs reference   oracle queries q03 to q18 answered on ids and with
#                --reference (the reference evaluator over the quads the
#                planner guard selects); equal as multisets
#                (tests/sbm11/compare_answers.py).
#   (d) gate     tests/sbm11/gate/gate.nq (default and named graphs, integer
#                types, a non-canonical integer, language tags, blank nodes)
#                packed and activated; each tests/sbm11/gate/*.rq answered by
#                `l4sbm11 query` and by the in-memory reference engine
#                (`l4factoidal query gate.nq`), equal as multisets. A query
#                named ids-* must run on ids (path=ids); one named ref-* must
#                take the reference fallback (path=reference): EXISTS and NOT
#                EXISTS outside the top group or over a pattern that is not a
#                basic graph pattern (issue 956), MINUS, sub-SELECT, the OPTIONAL shapes outside the id
#                fragment (nested, a variable two groups share that the base
#                does not bind, a FILTER in the group over a base variable,
#                OPTIONAL first, GRAPH in the group), EXISTS in a SELECT
#                expression, DESCRIBE, a FILTER inside GRAPH ?g over ?g, and
#                the other forms only the reference semantics decide
#                (CLAUDE.md anti-pattern 34). The ids-optional-* queries run
#                OPTIONAL on ids (issue 775): no match, one, several, FILTER
#                in the group true, false and an error, two groups, GRAPH in
#                the base, ORDER BY the optional variable (with LIMIT, so the
#                order is part of the answer), COUNT and GROUP BY over it,
#                DISTINCT, SELECT *. The ids-ask-*, ids-construct-*,
#                ids-expr-*, ids-agg-* and ids-filter-* queries run ASK,
#                CONSTRUCT, SELECT expressions, aggregates and FILTERs outside
#                Expr.backendLocal on ids (issue 823), with the error cases: a
#                FILTER error removes the row, an aggregate over an empty
#                group, an unbound variable in an expression.
#   (e) checks   `l4sbm11 prm-check` (the byte-array PRM1 decoder against the
#                list decoder of the round-trip theorem; and the PRM1 range
#                search of issue 805, PrmRange.rangeM, against decoding the
#                whole file and selecting, on 385 keys per PRM1 file, over the
#                bytes in memory and through query sessions under --verify
#                none and merkle) and `l4sbm11 frame-check` (the word decoder
#                against decodeColumnAt) on every PRM1 file and every frame of
#                the generation. The process time of a lookup on the DBpedia
#                slice is tests/sbm11/process-start.sh (issue 805).
#   (f) verify   q01 to q21 answered with --verify merkle and --verify none
#                (https://github.com/danbri/factoidal/issues/796): the
#                outputs must be byte-identical. Parts (a) to (e) use the
#                CLI default (none when a CURRENT pointer names GEN).
#   (h) delta    stage 5 (https://github.com/danbri/factoidal/issues/791):
#                the gate fixture packed, then the batches of
#                tests/sbm11/delta/gate-ops.txt sent one by one with
#                `l4sbm11 update`; after each batch every gate query and every
#                tests/sbm11/delta/*.rq (EXISTS, NOT EXISTS, MINUS, OPTIONAL
#                with FILTER on the changed rows) answered on the overlay and
#                by `l4factoidal query` over the state tests/sbm11/delta_apply.py
#                computes (a separate implementation over the quads' text);
#                equal as multisets, on the path the name says. Then a fresh
#                pack of the final state answers the same; `l4sbm11 compact`
#                writes a generation whose every artifact is byte-identical to
#                the fresh pack's; the compacted generation answers the same;
#                an update after compaction is seen (epoch 2); then DELETE WHERE
#                and INSERT DATA with a blank node are applied (until 2026-10-14
#                both were refused, https://github.com/danbri/factoidal/issues/849
#                and https://github.com/danbri/factoidal/issues/850), and the
#                state they leave, compacted and dumped, is isomorphic to the
#                state the reference engine computes for the same requests.
#   (i) olympics stage 5 on the olympics generation (a copy): the batches of
#                tests/sbm11/delta/olympics-ops.txt, the inserted row seen,
#                the deleted row not seen; q01 to q21 and
#                tests/sbm11/delta/olympics/*.rq on the overlay equal to a
#                fresh pack of the updated source; the compacted generation
#                byte-identical to the fresh pack; compaction time at most 1.2
#                times the fresh pack time. Needs QLVR_WORK/instance/olympics.nt;
#                SBM11_DELTA_OLYMPICS=0 leaves (i) out (printed, not counted).
#   (j) exact    the exact permutation check of activation (lemma L3b,
#                Harness/Sbm11PermCheck.lean, PermSet.perms_same): the gate
#                fixture is admitted with segment limits of 1, 3 and 1,000,000
#                rows (SBM11_VERIFY_GROUP_ROWS; 1 and 3 write sorted runs to
#                disk and merge them); a copy whose POS files come from a
#                pack of the fixture with one quad changed (same dictionary, same
#                row count, another quad set; resealed) is refused by the exact
#                check with the digest comparison off (SBM11_VERIFY_DIGEST=0)
#                and by the digest with it on; no run directory is left.
#   (k) scaling  tests/sbm11/phase2_scaling.sh: packer phase 2 (the k-way
#                merge of the term runs) on synthetic sources of 1, 2 and 4
#                million lines (244 to 836 term runs; median of 3 runs each,
#                CPU time of the merge thread); 4n at most 6.25 times n, 2.5
#                per doubling (https://github.com/danbri/factoidal/issues/804;
#                about 2 minutes). SBM11_PHASE2_SCALING=0 leaves (k) out
#                (printed, not counted).
#   (l) sip      sideways information passing
#                (https://github.com/danbri/factoidal/issues/809): the gate
#                fixture packed with blocks of 2 rows, every ids-* gate query
#                with `--sip always` (candidates whenever the join shape allows
#                them) against `l4factoidal query gate.nq`; each ids-sip-*
#                query must take a scan with candidates, and the run must
#                skip a block by its candidates. Then q01 to q21 and
#                tests/sbm11/sip/*.rq on olympics with --sip off, auto and
#                always, equal as multisets; each sip-*.rq takes a scan with
#                candidates under auto, sip-every-block one that skips no
#                block.
#   (m) rdf12    RDF 1.2 triple terms (https://github.com/danbri/factoidal/issues/792
#                item 1): tests/sbm11/gate12/gate12.nq (triple terms in the
#                object position, nested to depth 3, in the default graph and
#                in named graphs, with blank-node subjects, a directional
#                literal, an upper-case language tag, a non-canonical integer,
#                rdf:reifies) packed and activated; each tests/sbm11/gate12/*.rq
#                read with the SPARQL 1.2 grammar (--sparql12) and answered by
#                `l4sbm11 query`, by its reference fallback (--reference) and
#                by `l4factoidal query --format nquads12 --sparql12`, equal as
#                multisets; ids-* on path=ids (a triple term without variables
#                or blank nodes inside as a constant, the triple functions,
#                joins, GROUP BY, ORDER BY over triple terms), ref-* on
#                path=reference (a variable or a blank node inside a
#                triple-term pattern, a triple term as subject, EXISTS);
#                --reference-render byte-identical to the key printer; the
#                ids-* queries again on blocks of 2 rows with --sip always and
#                --threads 4; `dump` equal to `l4factoidal parse --format
#                nquads12 --out nquads` of the source, as sets, and `canon`
#                of the source (it reads RDF 1.2 through the source layer,
#                https://github.com/danbri/factoidal/issues/837);
#                `l4sbm11-dict-pack --check` with failures=0; after one update,
#                `compact` byte-identical to a fresh pack of the updated
#                quads. SPARQL 1.2 Update through the delta log (issue 792
#                item 1, the update part): a plain update (DLOG version 1),
#                then tests/sbm11/gate12/update/u1.ru to u3.ru with --sparql12
#                (triple terms, nested, in named graphs, directional
#                literals; the log gets version 2 in place); after each,
#                gate12/update/*.rq on its path and by --reference, equal as
#                multisets to `l4factoidal query --sparql12` over the state of
#                `l4factoidal update --sparql12`, and after u3 the 44
#                gate12/*.rq too; then two requests that were refused until
#                2026-10-14 (https://github.com/danbri/factoidal/issues/849 and
#                https://github.com/danbri/factoidal/issues/850), u4 (a blank node
#                inside a nested triple term in INSERT DATA) and u5 (DELETE WHERE
#                with a triple-term pattern that has a variable), checked the same
#                way; refusals that stay (a blank node inside a triple term of
#                DELETE DATA, a triple term without --sparql12) leave the log
#                unchanged; the compacted dump equals the reference state and
#                the compacted generation a fresh pack of it.
#   (n) layering  no module under formal/lean4/L4Factoidal/Storage/ imports an
#                L4Factoidal.Syntax module or names one in its code
#                (tests/sbm11/storage_layering.py). The store takes RDF quads from
#                the source layer (L4Factoidal/RDF/Source.lean) and does not know a
#                concrete syntax (owner, 2026-10-14,
#                https://github.com/danbri/factoidal/issues/837).
#   (o) syntax   tests/sbm11/syntax_independence.sh: one dataset written in
#                several syntaxes gives byte-identical SBM11 data files (the
#                manifests differ only in the source length and digest); blank
#                nodes compared by their RDFC-1.0 canonical N-Quads; labels of one
#                document stay distinct; no default syntax. Its counts are added
#                to this run's.
#   (p) w3c      tests/sbm11/w3c_roundtrip.sh: every positive evaluation test of
#                the W3C RDF suites (N-Triples, N-Quads, Turtle, TriG, RDF/XML;
#                RDF 1.1 and RDF 1.2) and of the JSON-LD toRdf manifest, and the
#                positive syntax tests, read from the manifests on disk, packed
#                with `l4sbm11-pack`, dumped with `l4sbm11 dump` and compared with
#                the result file by dataset isomorphism; the same parse without
#                the store is compared too. A test that the parser passes and the
#                store fails is a failure; the expected failures are rows of
#                tests/sbm11/w3c_roundtrip_xfail.tsv with an open issue (the run
#                fails when one passes). Nine empty documents pack to valid empty
#                generations. About 40 s with 4 jobs. Its counts are added to this
#                run's.
#   (q) export   tests/sbm11/export_roundtrip.sh: `l4sbm11 export` in each syntax
#                that can write the dataset, packed again, byte-identical data
#                files (blank nodes: equal RDFC-1.0 canonical N-Quads); the
#                refusals of a syntax with no graph name or no triple term; `--graph`,
#                `--out`, `--prefix`; empty generations; a 1 MB generated dataset.
#                Its counts are added to this run's.
#   (r) update   tests/sbm11/update_where.sh: DELETE WHERE, DELETE/INSERT with WITH,
#                USING and USING NAMED, template and INSERT DATA blank nodes, the graph
#                management operations, errors, the fresh blank node rule and SPARQL 1.2,
#                each request applied by `l4sbm11 update` and by the reference engine
#                (`l4factoidal update`), the states compared by isomorphism and the
#                queries on the overlay by value; the replay of the log in dictionary order
#                against one lookup for each term (issue 858); the size limit of the log (issue
#                851); the scaling of the update path (issues 857 and 858); every named
#                graph, also one with no triple and one named by a blank node (group
#                `graphs`; https://github.com/danbri/factoidal/issues/855 and
#                https://github.com/danbri/factoidal/issues/856); one expected failure
#                that names an open issue (https://github.com/danbri/factoidal/issues/803
#                item 4). Its counts are added to this run's.
#   (s) w3c-update  tests/sbm11/w3c_update.sh: the 94 W3C SPARQL 1.1 Update evaluation
#                tests, read from the manifests on disk, run through the store (pack the
#                initial Graph Store as TriG, `l4sbm11 update`, `l4sbm11 compact`, `l4sbm11
#                export --format trig`, compare by isomorphism with every named graph
#                compared, also one with no triple: issue 855) and through the in-memory
#                reference engine. The store passes every test the reference passes. Its
#                counts (the store's) are added to this run's, under their own line.
#   (t) agg-ids  tests/sbm11/agg_ids.sh (https://github.com/danbri/factoidal/issues/825):
#                the gate queries in the plan of `AggStream.aggPlan?` say "aggregated on
#                ids" in --explain and answer byte for byte as `--no-agg-ids` does (the
#                decoded rows and `selectPost`); the two gate queries whose group column
#                the plan does not admit (a dictionary literal, an unbound value) decode
#                the rows; six expected failures for the grouped shapes still decoded
#                (HAVING, DISTINCT aggregates, GROUP_CONCAT, an expression in GROUP BY, a
#                literal or an unbound value as the group key) and one for the values
#                held by the representative rows, each naming
#                https://github.com/danbri/factoidal/issues/861; DBpedia d19 when the
#                slice generation exists. Its counts are added to this run's.
#   (u) quad-source  tests/sbm11/quad_source.sh
#                (https://github.com/danbri/factoidal/issues/866): the packer entry
#                `packQuads` takes a producer of RDF quads (`QuadSource`), not a file path.
#                In-process checks of the producers (a Dataset, an array) and of the
#                entry (the generation does not depend on the number of producers, the
#                batch size, the term map size or the order of the quads); a Dataset
#                value in memory packed, dumped and compared with the dataset by
#                isomorphism and by RDFC-1.0; the Dataset route of the command line
#                (`--via-dataset`) byte-identical to the file route on every syntax
#                fixture; the triples of an HDT file packed with no text in between and
#                compared with the HDT store's own dump and with the file it was made
#                from. Parts (h), (i) and (m) also run `compact --via-quads`, the
#                reference route of compaction (the quads of the overlaid generation
#                decoded to terms and given to the packer's phase 1), and require
#                the same files as the default route. Its counts are added to this run's.
#   (v) graphs   tests/sbm11/named_graphs.sh (https://github.com/danbri/factoidal/issues/855
#                and https://github.com/danbri/factoidal/issues/856): the D5 fixture
#                (named graphs with no triple, graphs named by a blank node) packed, with
#                a log of DROP, CREATE, CLEAR and INSERT, with a log of CLEAR NAMED (DLOG
#                version 3), and compacted; in each state the queries of
#                tests/sbm11/graphs/ against the in-memory reference over the same
#                dataset (`l4sbm11-w3c query-source`, which keeps a graph with no
#                triple), each on the path its name says; `l4sbm11 graphs`; the TriG and
#                JSON-LD exports with the graphs with no triple compared; the notice of
#                the N-Quads export; the refusal of N-Triples; expected failures
#                that name open issues (`l4factoidal query` gives neither a graph
#                with no triple nor a graph named by a blank node, https://github.com/danbri/factoidal/issues/876;
#                the IBK4 and IBK5 stores lose a graph with no triple, https://github.com/danbri/factoidal/issues/880). Its
#                counts are added to this run's.
#   (w) permdisk tests/sbm11/perm_check_disk.sh: the temporary disk of the exact
#                permutation check (part (j)) is at most half the generation (issue 810), also when
#                it writes runs; more than a thousand runs are merged.
#   (g) tamper   a copy of the generation with one byte changed in a block
#                frame of spo.prb1 (manifest and sidecars kept): `scan` and
#                `query` must be refused under merkle (and by default, the
#                copy not being activated), and must answer with exit 0 and
#                other rows under none: the documented limit of none is
#                pinned, so a change of either behaviour fails the run.
#
# Usage: tests/sbm11/run.sh [GEN]   (default /home/user/qlvr-work/sbm11/s3/wfull,
# an activated olympics generation; tests/sbm11/stage3_check.sh makes one).
# Exit 0 only when every check passes; 2 when an input is missing.
# Env: QLVR_WORK                the QLever work directory (instance, oracle, generations)
#      FACTOIDAL_TESTING_ROOT   the directory of the W3C fixtures for parts (p), (s) and the
#                               HDT files of (u) (default third_party/testing of this tree);
#                               a git worktree has no submodules, and sets it to the
#                               checkout that has them
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin"
WORK="${QLVR_WORK:-/home/user/qlvr-work}"
GEN="${1:-$WORK/sbm11/s3/wfull}"
ORACLE="$WORK/oracle"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4factoidal" "$GEN" "$ORACLE"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-run.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAILS=0
record() { # record <part> <name> <ok:0|1> <detail>
  if [ "$3" = 0 ]; then PASS=$((PASS + 1)); printf 'ok   %-8s %-34s %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'FAIL %-8s %-34s %s\n' "$1" "$2" "$4"; fi
}

echo "=== (a) oracle queries"
OP=0; OF=0
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  rc=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" >"$TMP/$n.srj" 2>"$TMP/$n.err" || rc=$?
  if [ "$rc" -ne 0 ]; then
    record oracle "$n" 1 "exit $rc: $(tail -1 "$TMP/$n.err")"; OF=$((OF + 1)); continue
  fi
  v="$(python3 -I "$HERE/compare_oracle.py" "$ORACLE/$n.srj" "$TMP/$n.srj" "$rq" "$n" 2>&1)"; c=$?
  p="$(grep -o 'path=[a-z]*' "$TMP/$n.err")"
  record oracle "$n" "$c" "$p; $(printf '%s' "$v" | head -1)"
  if [ "$c" = 0 ]; then OP=$((OP + 1)); else OF=$((OF + 1)); fi
done
echo "oracle: $OP pass, $OF fail (out of $((OP + OF)))"

echo "=== (b) key printer against jsonOfTerm"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --reference-render >"$TMP/$n.ref" 2>/dev/null
  if cmp -s "$TMP/$n.srj" "$TMP/$n.ref"; then record render "$n" 0 "byte-identical ($(wc -c <"$TMP/$n.srj") bytes)"
  else record render "$n" 1 "outputs differ"; fi
done

echo "=== (c) the id path against the reference fallback"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  case $n in q0[3-9]*|q1[0-8]*) ;; *) continue ;; esac
  rc=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --reference >"$TMP/$n.fb" 2>"$TMP/$n.fberr" || rc=$?
  if [ "$rc" -ne 0 ]; then record ids-ref "$n" 1 "fallback exit $rc"; continue; fi
  v="$(python3 -I "$HERE/compare_answers.py" "$TMP/$n.srj" "$TMP/$n.fb" 0)"
  case "$v" in equal*) record ids-ref "$n" 0 "$v; $(grep -o 'quads=[0-9]*' "$TMP/$n.fberr")" ;; *) record ids-ref "$n" 1 "$v" ;; esac
done

echo "=== (d) gate fixture: id path and reference fallback against l4factoidal"
G="$TMP/gate"
rc=0
"$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$G/gen" --workers 1 >"$TMP/gpack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G" gen >"$TMP/gact.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  record gate pack-activate 1 "exit $rc: $(tail -1 "$TMP/gpack.log" "$TMP/gact.log" 2>/dev/null | tr '\n' ' ')"
else
  for rq in "$HERE"/gate/*.rq; do
    n="$(basename "$rq" .rq)"
    qb="file://$(realpath "$rq")"
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$G" --file "$rq" --base "$qb" >"$TMP/g-$n.got" 2>"$TMP/g-$n.err" || rc=$?
    if [ "$rc" -ne 0 ]; then record gate "$n" 1 "exit $rc: $(tail -1 "$TMP/g-$n.err")"; continue; fi
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$HERE/gate/gate.nq" --format nquads --query "$rq" \
      >"$TMP/g-$n.want" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$TMP/g-$n.got" "$TMP/g-$n.want" "$rrc")"
    p="$(grep -o 'path=[a-z]*' "$TMP/g-$n.err")"
    want_path=path=ids; case $n in ref-*) want_path=path=reference ;; esac
    if [ "$p" != "$want_path" ]; then record gate "$n" 1 "$p, expected $want_path"
    else case "$v" in equal*) record gate "$n" 0 "$p; $v" ;; *) record gate "$n" 1 "$p; $v" ;; esac
    fi
  done
fi

echo "=== (e) decoder checks on every PRM1 file and frame"
if out="$("$BIN/l4sbm11" prm-check "$GEN" 2>&1)"; then record checks prm-check 0 "$(printf '%s' "$out" | tr '\n' ' ' | head -c 150)"
else record checks prm-check 1 "$out"; fi
if out="$("$BIN/l4sbm11" frame-check "$GEN" 2>&1)"; then record checks frame-check 0 "$out"
else record checks frame-check 1 "$out"; fi

echo "=== (f) the same answers under --verify merkle and --verify none"
for rq in "$ROOT"/tests/qlvr/queries/q*.rq; do
  n="$(basename "$rq" .rq)"
  rm=0; rn=0
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --verify merkle >"$TMP/$n.vm" 2>"$TMP/$n.vmerr" || rm=$?
  timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --verify none >"$TMP/$n.vn" 2>"$TMP/$n.vnerr" || rn=$?
  if [ "$rm" -ne 0 ] || [ "$rn" -ne 0 ]; then record verify "$n" 1 "exit merkle $rm, none $rn"
  elif ! grep -q 'verify=merkle' "$TMP/$n.vmerr" || ! grep -q 'verify=none' "$TMP/$n.vnerr"; then
    record verify "$n" 1 "stderr does not name the verify option"
  elif cmp -s "$TMP/$n.vm" "$TMP/$n.vn"; then
    record verify "$n" 0 "byte-identical; fetched merkle $(grep -o 'range bytes fetched [0-9]*' "$TMP/$n.vmerr" | grep -o '[0-9]*$'), none $(grep -o 'range bytes fetched [0-9]*' "$TMP/$n.vnerr" | grep -o '[0-9]*$')"
  else record verify "$n" 1 "outputs differ"; fi
done

echo "=== (g) a changed byte in a block frame: refused under merkle, NOT detected under none"
# The documented limit of --verify none (https://github.com/danbri/factoidal/issues/796):
# it relies on activation, so a byte changed after activation is read as data.
# Both halves are asserted, so a change of either behaviour turns this RED.
SRC="$GEN"; [ -f "$GEN/CURRENT" ] && SRC="$GEN/$(cat "$GEN/CURRENT")"
T="$TMP/tamper"
rc=0; cp -r "$SRC" "$T" || rc=$?
if [ "$rc" -ne 0 ]; then record tamper copy 1 "cp exit $rc"
else
  # SPO block 0, column 2 (objects, a delta frame): the object of row 1 (the
  # second quad of the first subject) becomes another id k away, the deltas
  # of rows 1 and 2 re-encoded with the same byte length. Rows stay strictly
  # increasing and the first and last rows, which the reader compares with
  # PRM1, do not change, so the frame decodes without error.
  if ! python3 -I -c 'import sys
d = sys.argv[1]
m = open(d + "/spo.prm1", "rb").read()
le = lambda b: int.from_bytes(b, "little")
e = 22
rows, off = le(m[e + 64:e + 68]), le(m[e + 68:e + 76])
l0, l1, l2 = le(m[e + 76:e + 80]), le(m[e + 80:e + 84]), le(m[e + 84:e + 88])
b = bytearray(open(d + "/spo.prb1", "rb").read())
f = off + l0 + l1
if b[f] != 2 or rows < 3: sys.exit("SPO block 0 column 2 is not a delta frame of 3 or more rows")
def var(n):
    out = [n % 128]; n //= 128
    while n: out.append(128 | (n % 128)); n //= 128
    return bytes(reversed(out))
zz = lambda p, v: 2 * (v - p) if p <= v else 2 * (p - v) - 1
vals, i, prev = [], f + 1, 0
for _ in range(rows):
    z = 0
    while True:
        z = z * 128 + (b[i] & 127); i += 1
        if b[i - 1] < 128: break
    prev = prev + z // 2 if z % 2 == 0 else prev - (z + 1) // 2
    vals.append(prev)
old = b"".join(var(zz(p, v)) for p, v in zip([0] + vals, vals))
if old != bytes(b[f + 1:f + l2]): sys.exit("the frame does not re-encode")
for k in (1, -1, 2, -2, 3, -3, 4, -4):
    new = list(vals); new[1] += k
    enc = b"".join(var(zz(p, v)) for p, v in zip([0] + new, new))
    if len(enc) == len(old):
        b[f + 1:f + l2] = enc
        open(d + "/spo.prb1", "wb").write(b); sys.exit(0)
sys.exit("no change of the same length")' "$T" 2>"$TMP/t-flip.err"; then
    record tamper flip 1 "$(cat "$TMP/t-flip.err")"
  fi
  sm=0; "$BIN/l4sbm11" scan "$T" spo --ids --limit 5 --verify merkle >"$TMP/t-m.out" 2>"$TMP/t-m.err" || sm=$?
  if [ "$sm" -ne 0 ] && grep -q 'refused' "$TMP/t-m.err"; then record tamper scan-merkle 0 "refused (exit $sm)"
  else record tamper scan-merkle 1 "exit $sm: $(tail -1 "$TMP/t-m.err")"; fi
  sd=0; "$BIN/l4sbm11" scan "$T" spo --ids --limit 5 >"$TMP/t-d.out" 2>"$TMP/t-d.err" || sd=$?
  if [ "$sd" -ne 0 ] && grep -q 'verify=merkle\|refused' "$TMP/t-d.err"; then record tamper default-not-activated 0 "a directory no CURRENT names: merkle, refused"
  else record tamper default-not-activated 1 "exit $sd: $(tail -1 "$TMP/t-d.err")"; fi
  "$BIN/l4sbm11" scan "$SRC" spo --ids --limit 5 --verify none >"$TMP/t-orig.out" 2>/dev/null
  sn=0; "$BIN/l4sbm11" scan "$T" spo --ids --limit 5 --verify none >"$TMP/t-n.out" 2>"$TMP/t-n.err" || sn=$?
  if [ "$sn" -eq 0 ] && [ -s "$TMP/t-n.out" ] && ! cmp -s "$TMP/t-n.out" "$TMP/t-orig.out"; then
    record tamper scan-none 0 "not detected: exit 0, other ids than the original (documented limit)"
  else record tamper scan-none 1 "exit $sn; expected exit 0 and changed rows"; fi
  # the first subject of SPO, bound: the plan reads SPO block 0
  S="$("$BIN/l4sbm11" scan "$SRC" spo --limit 1 --verify none 2>/dev/null | sed 's/^\(<[^>]*>\).*/\1/')"
  Q="SELECT ?p ?o WHERE { $S ?p ?o }"
  qm=0; "$BIN/l4sbm11" query "$T" "$Q" --verify merkle >"$TMP/t-qm.out" 2>"$TMP/t-qm.err" || qm=$?
  if [ "$qm" -ne 0 ] && grep -q 'refused' "$TMP/t-qm.err"; then record tamper query-merkle 0 "refused (exit $qm)"
  else record tamper query-merkle 1 "exit $qm: $(tail -1 "$TMP/t-qm.err")"; fi
  "$BIN/l4sbm11" query "$SRC" "$Q" --verify none >"$TMP/t-qo.out" 2>/dev/null
  qn=0; "$BIN/l4sbm11" query "$T" "$Q" --verify none >"$TMP/t-qn.out" 2>"$TMP/t-qn.err" || qn=$?
  if [ "$qn" -eq 0 ] && ! cmp -s "$TMP/t-qn.out" "$TMP/t-qo.out"; then
    record tamper query-none 0 "not detected: exit 0, other answer than the original (documented limit)"
  else record tamper query-none 1 "exit $qn: $(tail -1 "$TMP/t-qn.err"); expected exit 0 and a changed answer"; fi
fi
if [ -f "$GEN/CURRENT" ]; then
  "$BIN/l4sbm11" query "$GEN" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' --explain >/dev/null 2>"$TMP/def.err"
  if grep -q 'plan: verify=none (default' "$TMP/def.err"; then record tamper default-activated 0 "GEN has CURRENT: verify=none by default"
  else record tamper default-activated 1 "$(grep 'verify' "$TMP/def.err" | head -1)"; fi
fi

# --- stage 5 ----------------------------------------------------------------
# run_q <gen> <rq> <out> <err>: one query on a generation, exit code in $QRC
run_q() {
  QRC=0
  timeout 600 "$BIN/l4sbm11" query "$1" --file "$2" --base "file://$(realpath "$2")" >"$3" 2>"$4" || QRC=$?
}
# want_path <name>: the path a query named ref-* must take (path=reference);
# every other query, path=ids
want_path() { case $1 in ref-*) echo path=reference ;; *) echo path=ids ;; esac; }
ARTS="dict.gdv1 dict.gdx1 pso.prb1 pso.prm1 pos.prb1 pos.prm1 spo.prb1 spo.prm1 osp.prb1 osp.prm1"
# same_artifacts <dirA> <dirB>: every artifact and its .merkle sidecar byte-identical; the
# graph list (graphs.gnl1, a generation that has a named graph) is in both or in neither
same_artifacts() {
  local a n=0
  for a in $ARTS graphs.gnl1; do
    if [ "$a" = graphs.gnl1 ] && [ ! -e "$1/$a" ] && [ ! -e "$2/$a" ]; then continue; fi
    cmp -s "$1/$a" "$2/$a" || { echo "$a differs"; return 1; }
    cmp -s "$1/$a.merkle" "$2/$a.merkle" || { echo "$a.merkle differs"; return 1; }
    n=$((n + 1))
  done
  echo "$n artifacts and their .merkle sidecars byte-identical"
}

echo "=== (h) delta overlay on the gate fixture"
H="$TMP/delta"
mkdir -p "$H"
"$BIN/l4sbm11" canon "$HERE/gate/gate.nq" >"$H/base.nq"
NB="$(python3 -I "$HERE/delta_apply.py" "$H/base.nq" "$HERE/delta/gate-ops.txt" "$H/ops")"
rc=0
"$BIN/l4sbm11-pack" "$H/base.nq" "$H/col/gen" --workers 1 >"$H/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$H/col" gen >"$H/act.log" 2>&1 || rc=$?; }
GQ="$(ls "$HERE"/gate/*.rq "$HERE"/delta/*.rq)"
# check_all <gen> <reference.nq> <label> [<directory to keep the answers in>]
check_all() {
  local bad="" n=0 nq rrc v
  for rq in $GQ; do
    nq="$(basename "$rq" .rq)"
    n=$((n + 1))
    run_q "$1" "$rq" "$H/got.srj" "$H/got.err"
    if [ "$QRC" -ne 0 ]; then bad="$bad $nq(exit $QRC)"; continue; fi
    [ -n "${4:-}" ] && cp "$H/got.srj" "$4/$nq.srj"
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$2" --format nquads --query "$rq" >"$H/want.srj" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$H/got.srj" "$H/want.srj" "$rrc")"
    case "$v" in equal*) ;; *) bad="$bad $nq($v)"; continue ;; esac
    if [ "$(grep -o 'path=[a-z]*' "$H/got.err")" != "$(want_path "$nq")" ]; then bad="$bad $nq(path)"; fi
  done
  if [ -z "$bad" ]; then record delta "$3" 0 "$n queries equal to the reference engine, each on its path"
  else record delta "$3" 1 "failed:$bad"; fi
}
if [ "$rc" -ne 0 ]; then
  record delta pack-activate 1 "exit $rc"
else
  for k in $(seq 1 "$NB"); do
    urc=0
    "$BIN/l4sbm11" update "$H/col" "$(cat "$H/ops/batch-$k.ru")" >"$H/upd-$k.log" 2>&1 || urc=$?
    if [ "$urc" -ne 0 ]; then record delta "batch-$k-update" 1 "exit $urc: $(tail -1 "$H/upd-$k.log")"; continue; fi
    check_all "$H/col" "$H/ops/after-$k.nq" "batch-$k"
  done
  # the overlay's answers after the last batch, kept for the comparisons below
  mkdir -p "$H/ans-overlay" "$H/ans-fresh"
  check_all "$H/col" "$H/ops/final.nq" "final-overlay" "$H/ans-overlay"
  rc=0
  "$BIN/l4sbm11-pack" "$H/ops/final.nq" "$H/fresh" --workers 1 >"$H/fresh.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record delta fresh-pack 1 "exit $rc"; fi
  bad=""
  for rq in $GQ; do
    nq="$(basename "$rq" .rq)"
    run_q "$H/fresh" "$rq" "$H/ans-fresh/$nq.srj" "$H/f.err"
    v="$(python3 -I "$HERE/compare_answers.py" "$H/ans-overlay/$nq.srj" "$H/ans-fresh/$nq.srj" "$QRC")"
    case "$v" in equal*) ;; *) bad="$bad $nq($v)" ;; esac
  done
  if [ -z "$bad" ]; then record delta overlay-vs-fresh-pack 0 "$(echo $GQ | wc -w) queries: overlay answers equal a fresh pack of the updated data"
  else record delta overlay-vs-fresh-pack 1 "differ:$bad"; fi
  crc=0
  "$BIN/l4sbm11" compact "$H/col" "$H/col/gen2" >"$H/compact.log" 2>&1 || crc=$?
  if [ "$crc" -ne 0 ]; then record delta compact 1 "exit $crc: $(tail -1 "$H/compact.log")"
  else
    v="$(same_artifacts "$H/col/gen2" "$H/fresh")"; c=$?
    record delta compact-equals-fresh-pack "$c" "$v"
    # the reference route of compaction (issue 866 item 3): the quads of the overlaid
    # generation decoded to RDF terms and given to the packer's phase 1
    cqrc=0
    "$BIN/l4sbm11" compact "$H/col" "$H/viaq" --via-quads >"$H/compactq.log" 2>&1 || cqrc=$?
    if [ "$cqrc" -ne 0 ]; then record delta compact-via-quads 1 "exit $cqrc: $(tail -1 "$H/compactq.log")"
    else
      v="$(same_artifacts "$H/viaq" "$H/col/gen2")"; c=$?
      record delta compact-via-quads-equals-default "$c" "$v"
    fi
    "$BIN/l4sbm11" activate "$H/col" gen2 >"$H/act2.log" 2>&1 || record delta activate-compacted 1 "$(tail -1 "$H/act2.log")"
    check_all "$H/col" "$H/ops/final.nq" "compacted"
    run_q "$H/col" "$HERE/delta/ids-upd-count.rq" "$H/c.srj" "$H/c.err"
    if grep -q 'delta batches 0' "$H/c.err"; then record delta compacted-no-replay 0 "the compacted generation replays no batch"
    else record delta compacted-no-replay 1 "$(grep -o 'delta batches [0-9]*' "$H/c.err")"; fi
    urc=0
    "$BIN/l4sbm11" update "$H/col" 'INSERT DATA { <http://ex.org/after> <http://ex.org/name> "after compaction" }' >"$H/upd-after.log" 2>&1 || urc=$?
    "$BIN/l4sbm11" query "$H/col" 'SELECT ?n WHERE { <http://ex.org/after> <http://ex.org/name> ?n }' >"$H/after.srj" 2>/dev/null
    if [ "$urc" -eq 0 ] && grep -q 'epoch=2' "$H/upd-after.log" && grep -q 'after compaction' "$H/after.srj"; then
      record delta update-after-compaction 0 "epoch 2 batch committed and seen"
    else record delta update-after-compaction 1 "exit $urc: $(tail -1 "$H/upd-after.log")"; fi
  fi
  # the former stage 5 limits (https://github.com/danbri/factoidal/issues/849 and
  # https://github.com/danbri/factoidal/issues/850): DELETE WHERE and INSERT DATA with a blank node are
  # applied, and the state they leave is the reference engine's state for the same requests
  printf '%s\n' 'INSERT DATA { <http://ex.org/after> <http://ex.org/name> "after compaction" }' >"$H/ra1.ru"
  printf '%s\n' 'DELETE WHERE { ?s <http://ex.org/name> ?n }' >"$H/ra2.ru"
  printf '%s\n' 'INSERT DATA { _:b <http://ex.org/name> "blank" }' >"$H/ra3.ru"
  rrc=0
  "$BIN/l4factoidal" update "$H/ops/final.nq" --format nquads --update "$H/ra1.ru" >"$H/rs1.nq" 2>/dev/null || rrc=$?
  if [ "$rrc" -eq 0 ]; then "$BIN/l4factoidal" update "$H/rs1.nq" --format nquads --update "$H/ra2.ru" >"$H/rs2.nq" 2>/dev/null || rrc=$?; fi
  if [ "$rrc" -eq 0 ]; then "$BIN/l4factoidal" update "$H/rs2.nq" --format nquads --update "$H/ra3.ru" >"$H/rs3.nq" 2>/dev/null || rrc=$?; fi
  r1=0; "$BIN/l4sbm11" update "$H/col" --file "$H/ra2.ru" >"$H/r1.log" 2>&1 || r1=$?
  if [ "$r1" -eq 0 ] && [ "$rrc" -eq 0 ]; then record delta delete-where-applies 0 "DELETE WHERE applied: $(grep -o 'where path=[a-z]*' "$H/r1.log" | head -1), $(grep -o 'ops=[0-9]*' "$H/r1.log")"
  else record delta delete-where-applies 1 "store exit $r1, reference exit $rrc: $(tail -1 "$H/r1.log")"; fi
  r2=0; "$BIN/l4sbm11" update "$H/col" --file "$H/ra3.ru" >"$H/r2.log" 2>&1 || r2=$?
  if [ "$r2" -eq 0 ]; then record delta insert-data-bnode-applies 0 "INSERT DATA with a blank node applied: $(grep -o 'ops=[0-9]*' "$H/r2.log")"
  else record delta insert-data-bnode-applies 1 "exit $r2: $(tail -1 "$H/r2.log")"; fi
  crc=0
  "$BIN/l4sbm11" compact "$H/col" "$H/col/gen3" >"$H/compact3.log" 2>&1 || crc=$?
  if [ "$crc" -eq 0 ] && [ "$rrc" -eq 0 ]; then
    "$BIN/l4sbm11" dump "$H/col/gen3" >"$H/dump3.nq" 2>/dev/null
    v="$("$BIN/l4sbm11-w3c" compare "$H/rs3.nq" "$H/dump3.nq" --expected nq --mode rdf11 2>&1)" || true
    case "$v" in
      pass*) record delta update-state-equals-reference 0 "$(wc -l <"$H/dump3.nq") quads, isomorphic to the reference state after the three requests" ;;
      *) record delta update-state-equals-reference 1 "$(printf '%s' "$v" | head -1 | cut -c1-200)" ;;
    esac
  else record delta update-state-equals-reference 1 "compact exit $crc, reference exit $rrc"; fi
fi

echo "=== (i) delta overlay and compaction on olympics"
OLY_SRC="$WORK/instance/olympics.nt"
if [ "${SBM11_DELTA_OLYMPICS:-1}" = 0 ]; then
  echo "(i) left out: SBM11_DELTA_OLYMPICS=0 (not counted)"
elif [ ! -f "$OLY_SRC" ]; then
  record olympics source 1 "missing: $OLY_SRC"
else
  O="$TMP/oly"
  SRCG="$GEN"; [ -f "$GEN/CURRENT" ] && SRCG="$GEN/$(cat "$GEN/CURRENT")"
  mkdir -p "$O/col" "$O/ans-overlay" "$O/ans-fresh"
  cp -r "$SRCG" "$O/col/gen" && rm -f "$O/col/gen/deltas.dlog" "$O/col/gen/compacted.epoch"
  "$BIN/l4sbm11" activate "$O/col" gen >"$O/act.log" 2>&1 || record olympics activate 1 "$(tail -1 "$O/act.log")"
  NO="$(python3 -I "$HERE/delta_apply.py" "$OLY_SRC" "$HERE/delta/olympics-ops.txt" "$O/ops" --final-only)"
  for k in $(seq 1 "$NO"); do
    urc=0
    "$BIN/l4sbm11" update "$O/col" "$(cat "$O/ops/batch-$k.ru")" >"$O/upd-$k.log" 2>&1 || urc=$?
    record olympics "batch-$k-update" "$urc" "$(tail -1 "$O/upd-$k.log" | cut -c1-140)"
  done
  OQ="$(ls "$ROOT"/tests/qlvr/queries/q*.rq "$HERE"/delta/olympics/*.rq)"
  for rq in $OQ; do
    nq="$(basename "$rq" .rq)"
    run_q "$O/col" "$rq" "$O/ans-overlay/$nq.srj" "$O/ans-overlay/$nq.err"
  done
  rows() { python3 -I -c 'import json,sys; print(len(json.load(open(sys.argv[1]))["results"]["bindings"]))' "$1" 2>/dev/null; }
  n1="$(rows "$O/ans-overlay/ids-seen-insert.srj")"
  if [ "$n1" = 1 ]; then record olympics insert-seen 0 "1 row"; else record olympics insert-seen 1 "$n1 rows"; fi
  n0="$(rows "$O/ans-overlay/ids-not-seen-delete.srj")"
  if [ "$n0" = 0 ]; then record olympics delete-not-seen 0 "0 rows"; else record olympics delete-not-seen 1 "$n0 rows"; fi
  echo "    overlay q19: $(grep -o 'execution [0-9.]* ms; total [0-9.]* ms; peak RSS (VmHWM): [0-9]* kB' "$O/ans-overlay/q19-scan-bound-predicate-iri.err")"
  prc=0
  t0=$(date +%s%N)
  "$BIN/l4sbm11-pack" "$O/ops/final.nq" "$O/fresh" >"$O/fresh.log" 2>&1 || prc=$?
  pwall=$(( ($(date +%s%N) - t0) / 1000000 ))
  rm -f "$O/ops/final.nq"
  crc=0
  t0=$(date +%s%N)
  "$BIN/l4sbm11" compact "$O/col" "$O/col/gen2" >"$O/compact.log" 2>&1 || crc=$?
  cwall=$(( ($(date +%s%N) - t0) / 1000000 ))
  if [ "$prc" -ne 0 ] || [ "$crc" -ne 0 ]; then
    record olympics pack-and-compact 1 "pack exit $prc, compact exit $crc: $(tail -1 "$O/compact.log")"
  else
    pms="$(grep -o 'total-ms=[0-9.]*' "$O/fresh.log" | cut -d= -f2)"
    cms="$(grep -o 'total-ms=[0-9.]*' "$O/compact.log" | cut -d= -f2)"
    ratio="$(python3 -I -c 'import sys; print(round(float(sys.argv[2]) / float(sys.argv[1]), 3))' "$pms" "$cms")"
    if python3 -I -c 'import sys; sys.exit(0 if float(sys.argv[1]) <= 1.2 else 1)' "$ratio"; then
      record olympics compact-time 0 "compact $cms ms, fresh pack $pms ms, ratio $ratio (limit 1.2); load $(cut -d' ' -f1-3 /proc/loadavg)"
    else
      record olympics compact-time 1 "compact $cms ms, fresh pack $pms ms, ratio $ratio: above 1.2"
    fi
    echo "    pack:    process wall $pwall ms; $(grep -o 'peak-rss=[0-9]* kB' "$O/fresh.log"); $(grep -o 'total-on-disk=[0-9]*' "$O/fresh.log")"
    echo "    compact: process wall $cwall ms; $(grep -o 'peak-rss=[0-9]* kB' "$O/compact.log"); $(grep -o 'total-on-disk=[0-9]*' "$O/compact.log")"
    grep 'ms=' "$O/compact.log" | sed 's/^/    /'
    v="$(same_artifacts "$O/col/gen2" "$O/fresh")"; c=$?
    record olympics compact-equals-fresh-pack "$c" "$v"
    # the reference route of compaction (issue 866 item 3), and what it costs
    cqrc=0
    t0=$(date +%s%N)
    "$BIN/l4sbm11" compact "$O/col" "$O/viaq" --via-quads >"$O/compactq.log" 2>&1 || cqrc=$?
    cqwall=$(( ($(date +%s%N) - t0) / 1000000 ))
    if [ "$cqrc" -ne 0 ]; then record olympics compact-via-quads 1 "exit $cqrc: $(tail -1 "$O/compactq.log")"
    else
      v="$(same_artifacts "$O/viaq" "$O/col/gen2")"; c=$?
      record olympics compact-via-quads-equals-default "$c" "$v"
      echo "    compact --via-quads: process wall $cqwall ms (default route $cwall ms); $(grep -o 'peak-rss=[0-9]* kB' "$O/compactq.log")"
    fi
    bad=""
    for rq in $OQ; do
      nq="$(basename "$rq" .rq)"
      run_q "$O/fresh" "$rq" "$O/ans-fresh/$nq.srj" "$O/ans-fresh/$nq.err"
      v="$(python3 -I "$HERE/compare_answers.py" "$O/ans-overlay/$nq.srj" "$O/ans-fresh/$nq.srj" "$QRC")"
      case "$v" in equal*) ;; *) bad="$bad $nq($v)" ;; esac
      p="$(grep -o 'path=[a-z]*' "$O/ans-overlay/$nq.err")"
      case $nq in ref-*|ids-*) [ "$p" = "$(want_path "$nq")" ] || bad="$bad $nq($p)" ;; esac
    done
    if [ -z "$bad" ]; then record olympics overlay-vs-fresh-pack 0 "$(echo $OQ | wc -w) queries equal (q01 to q21 and the delta queries)"
    else record olympics overlay-vs-fresh-pack 1 "differ:$bad"; fi
  fi
fi

echo "=== (l) sideways information passing (issue 809)"
L="$TMP/sip"
mkdir -p "$L"
# (l1) the gate fixture packed with blocks of 2 rows, so that candidates skip
# blocks and key ranges cross blocks; every ids-* gate query with --sip always
# (candidates whenever the join shape allows them) against the reference engine
rc=0
"$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$L/col/gen" --workers 1 --block-rows 2 >"$L/pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$L/col" gen >"$L/act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  record sip gate-pack 1 "exit $rc: $(tail -1 "$L/pack.log" "$L/act.log" 2>/dev/null | tr '\n' ' ')"
else
  n=0; bad=""; sw=0; skipped=0
  for rq in "$HERE"/gate/ids-*.rq; do
    nq="$(basename "$rq" .rq)"
    n=$((n + 1))
    qrc=0
    timeout 120 "$BIN/l4sbm11" query "$L/col" --file "$rq" --base "file://$(realpath "$rq")" --sip always --explain \
      >"$L/$nq.got" 2>"$L/$nq.err" || qrc=$?
    if [ "$qrc" -ne 0 ]; then bad="$bad $nq(exit $qrc)"; continue; fi
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$HERE/gate/gate.nq" --format nquads --query "$rq" >"$L/$nq.want" 2>/dev/null || rrc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$L/$nq.got" "$L/$nq.want" "$rrc")"
    case "$v" in equal*) ;; *) bad="$bad $nq($v)" ;; esac
    grep -q 'path=ids' "$L/$nq.err" || bad="$bad $nq(path)"
    c="$(grep -c 'sideways' "$L/$nq.err")"; sw=$((sw + c))
    s="$(grep -o 'blocks skipped [0-9]*' "$L/$nq.err" | awk '{t += $3} END {print t + 0}')"; skipped=$((skipped + s))
  done
  if [ -z "$bad" ]; then
    record sip gate-always 0 "$n ids-* queries, --sip always, blocks of 2 rows: equal to the reference engine; $sw scans with candidates, $skipped blocks skipped"
  else record sip gate-always 1 "failed:$bad"; fi
  for rq in "$HERE"/gate/ids-sip-*.rq; do
    nq="$(basename "$rq" .rq)"
    if grep -q 'sideways' "$L/$nq.err"; then record sip "$nq" 0 "$(grep -o 'sideways [^;]*' "$L/$nq.err" | head -1)"
    else record sip "$nq" 1 "no scan with candidates"; fi
  done
  if [ "$sw" -gt 0 ] && [ "$skipped" -gt 0 ]; then record sip gate-coverage 0 "scans with candidates and skipped blocks both seen"
  else record sip gate-coverage 1 "scans with candidates $sw, blocks skipped $skipped: expected both above 0"; fi
  # (l1b) issue 929: ids-strstarts-window (answer checked above) scans POS
  # and does not read the blocks whose object ids the STRSTARTS rank test
  # rejects
  w="$(grep -o 'FILTER window on the scan column: [0-9]* of [0-9]*' "$L/ids-strstarts-window.err")"
  if ! grep -q 'streamed: pos key 1' "$L/ids-strstarts-window.err"; then
    record window gate-strstarts 1 "not a POS scan: $(grep -o 'streamed: [a-z]* key [0-9]*' "$L/ids-strstarts-window.err")"
  else case "$w" in
    ""|*": 0 of "*) record window gate-strstarts 1 "no block skipped: '$w'" ;;
    *) record window gate-strstarts 0 "$w (blocks of 2 rows, POS)" ;;
  esac; fi
  # (l1c) issue 930: ids-sip-date-filter (answer checked above, the shape of
  # DBpedia d14) passes candidates into the ex:when scan, whose join column
  # is a delta frame decoded by the word loop (Sip.deltaFindGoW)
  wl="$(grep -o 'key values tested [0-9]* (on words in [0-9]* blocks)' "$L/ids-sip-date-filter.err" | head -1)"
  case "$wl" in
    ""|*"in 0 blocks"*) record sip gate-word-loop 1 "no block decoded on words: '$wl'" ;;
    *) record sip gate-word-loop 0 "$wl (blocks of 2 rows)" ;;
  esac
  # (l1c) issue 932: a COUNT with no FILTER, no GROUP BY and no overlay takes
  # the rows of the blocks its PRM1 entry decides from the entry. Fixture of 32
  # default-graph triples packed in blocks of 10 rows: per permutation three
  # full blocks of 10 rows with a constant graph frame and one block of 2
  # rows (graph frame not provably constant: read). Equal to the reference
  # engine; the all-variable count decides at least one block and reads one;
  # the first four take the PRM1 count.
  M="$L/meta"
  mkdir -p "$M"
  mrc=0
  "$BIN/l4sbm11-pack" "$HERE/gate/count-meta.nq" "$M/col/gen" --workers 1 --block-rows 10 >"$M/pack.log" 2>&1 || mrc=$?
  [ "$mrc" -eq 0 ] && { "$BIN/l4sbm11" activate "$M/col" gen >"$M/act.log" 2>&1 || mrc=$?; }
  if [ "$mrc" -ne 0 ]; then record meta-count pack 1 "exit $mrc"
  else
    bad=""; mk=0; mline=""
    for q in 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' \
             'SELECT (COUNT(*) AS ?n) WHERE { ?s <http://example.org/p2> ?o }' \
             'SELECT (COUNT(*) AS ?n) WHERE { ?s <http://example.org/p4> ?o }' \
             'SELECT (COUNT(?o) AS ?n) WHERE { <http://example.org/s1> ?p ?o }' \
             'SELECT (COUNT(*) AS ?n) WHERE { ?s <http://example.org/p9> ?o }'; do
      mk=$((mk + 1))
      printf '%s\n' "$q" >"$M/q.rq"
      qrc=0
      timeout 120 "$BIN/l4sbm11" query "$M/col" --file "$M/q.rq" --explain >"$M/got.$mk" 2>"$M/err.$mk" || qrc=$?
      rrc=0
      timeout 120 "$BIN/l4factoidal" query "$HERE/gate/count-meta.nq" --format nquads --query "$M/q.rq" >"$M/want.$mk" 2>/dev/null || rrc=$?
      v="$(python3 -I "$HERE/compare_answers.py" "$M/got.$mk" "$M/want.$mk" "$rrc")"
      case "$qrc:$v" in 0:equal*) ;; *) bad="$bad [$q]($qrc $v)" ;; esac
      # the last query names a predicate with no id: its pattern is empty
      # before any scan
      [ "$mk" -eq 5 ] || grep -q 'from PRM1 entries' "$M/err.$mk" || bad="$bad [$q](no PRM1 count)"
      [ "$mk" -eq 1 ] && mline="$(grep -o 'from PRM1 entries ([0-9]* blocks decided by their entries)[^;]*; blocks [0-9]* read' "$M/err.$mk")"
    done
    if [ -n "$bad" ]; then record meta-count queries 1 "failed:$bad"
    else case "$mline" in
      *"(0 blocks"*|*"blocks 0 read"|"") record meta-count queries 1 "count of all: expected decided and read blocks: '$mline'" ;;
      *) record meta-count queries 0 "5 COUNT queries equal to the reference engine; count of all: $mline" ;;
    esac; fi
  fi
fi
# (l2) olympics: q01 to q21 and tests/sbm11/sip/*.rq with --sip off, auto (the
# default) and always, equal as multisets (a hash join may change the row
# order); every sip-*.rq takes a scan with candidates under auto, and
# sip-every-block one in which no block is skipped
bad=""; n=0
for rq in "$ROOT"/tests/qlvr/queries/q*.rq "$HERE"/sip/*.rq; do
  nq="$(basename "$rq" .rq)"
  n=$((n + 1))
  for m in off auto always; do
    qrc=0
    timeout 600 "$BIN/l4sbm11" query "$GEN" --file "$rq" --sip $m --explain >"$L/o-$nq.$m" 2>"$L/o-$nq.$m.err" || qrc=$?
    [ "$qrc" -eq 0 ] || bad="$bad $nq($m exit $qrc)"
  done
  for m in auto always; do
    v="$(python3 -I "$HERE/compare_answers.py" "$L/o-$nq.$m" "$L/o-$nq.off" 0)"
    case "$v" in equal*) ;; *) bad="$bad $nq($m: $v)" ;; esac
  done
  case $nq in sip-*) grep -q 'sideways' "$L/o-$nq.auto.err" || bad="$bad $nq(no scan with candidates)" ;; esac
done
if [ -z "$bad" ]; then record sip olympics-modes 0 "$n queries: --sip auto and always equal to off"
else record sip olympics-modes 1 "failed:$bad"; fi
if grep -q 'sideways ?a: [0-9]* candidates, blocks skipped 0' "$L/o-sip-every-block.auto.err"; then
  record sip every-block 0 "$(grep -o 'sideways ?a: [^;]*' "$L/o-sip-every-block.auto.err")"
else record sip every-block 1 "$(grep -o 'sideways [^;]*' "$L/o-sip-every-block.auto.err" | tr '\n' ' ')"; fi

echo "=== (j) the exact permutation check of activation (lemma L3b)"
J="$TMP/exact"
mkdir -p "$J"
# B: the gate fixture with one quad changed to another quad over the same
# terms (same dictionary, same row count, another quad set)
sed 's|^<http://ex.org/a> <http://ex.org/knows> <http://ex.org/b> \.$|<http://ex.org/a> <http://ex.org/knows> <http://ex.org/d> .|' \
  "$HERE/gate/gate.nq" >"$J/b.nq"
if cmp -s "$HERE/gate/gate.nq" "$J/b.nq"; then
  record exact fixture 1 "the sed did not change gate.nq"
else
  rc=0
  "$BIN/l4sbm11-pack" "$HERE/gate/gate.nq" "$J/a" --workers 1 --block-rows 2 >"$J/pa.log" 2>&1 || rc=$?
  "$BIN/l4sbm11-pack" "$J/b.nq" "$J/b" --workers 1 --block-rows 2 >"$J/pb.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record exact pack 1 "exit $rc"
  elif ! cmp -s "$J/a/dict.gdv1" "$J/b/dict.gdv1"; then record exact same-dictionary 1 "GDV1 differs"
  else
    # blocks of two rows; groups of 1 row (one block each), 3 rows, all rows
    for gr in 1 3 1000000; do
      vrc=0
      SBM11_VERIFY_GROUP_ROWS=$gr "$BIN/l4sbm11" verify "$J/a" >"$J/va-$gr.log" 2>&1 || vrc=$?
      if [ "$vrc" -eq 0 ] && grep -q "exact permutation check: segments=[0-9]* runs=[0-9]* group-rows=$gr digest=on failures=0" "$J/va-$gr.log"; then
        record exact "admitted-group-rows-$gr" 0 "$(grep -o 'segments=[0-9]* runs=[0-9]*' "$J/va-$gr.log")"
      else record exact "admitted-group-rows-$gr" 1 "exit $vrc: $(grep 'FAIL\|exact' "$J/va-$gr.log" | head -2 | tr '\n' ' ')"; fi
    done
    # A with the POS files of B: same row count, same ids, another quad set
    cp -r "$J/a" "$J/t"
    cp "$J/b/pos.prb1" "$J/b/pos.prm1" "$J/t/"
    "$BIN/l4sbm11" reseal "$J/t" >/dev/null 2>&1
    for gr in 1 1000000; do
      vrc=0
      SBM11_VERIFY_DIGEST=0 SBM11_VERIFY_GROUP_ROWS=$gr "$BIN/l4sbm11" verify "$J/t" >"$J/vt-$gr.log" 2>&1 || vrc=$?
      if [ "$vrc" -ne 0 ] && grep -q "FAIL: pos holds other quads than pso" "$J/vt-$gr.log" \
          && grep -q "digest=off failures=1" "$J/vt-$gr.log"; then
        record exact "refused-digest-off-$gr" 0 "$(grep -o 'FAIL: pos.*' "$J/vt-$gr.log" | head -1)"
      else record exact "refused-digest-off-$gr" 1 "exit $vrc: $(grep 'FAIL\|exact' "$J/vt-$gr.log" | head -2 | tr '\n' ' ')"; fi
    done
    vrc=0
    "$BIN/l4sbm11" verify "$J/t" >"$J/vt-d.log" 2>&1 || vrc=$?
    if [ "$vrc" -ne 0 ] && grep -q "holds other quads than pso (digest)" "$J/vt-d.log"; then
      record exact refused-digest-on 0 "the digest refuses it too"
    else record exact refused-digest-on 1 "exit $vrc"; fi
    # no run directory is left next to the generation
    left="$(ls -d "$J"/*.verify-* 2>/dev/null | wc -l)"
    if [ "$left" = 0 ]; then record exact temp-removed 0 "no run directory left"
    else record exact temp-removed 1 "$left left"; fi
  fi
fi

echo "=== (k) packer merge scaling (issue 804)"
if [ "${SBM11_PHASE2_SCALING:-1}" = 0 ]; then
  echo "(k) left out: SBM11_PHASE2_SCALING=0 (not counted)"
else
  rc=0
  SBM11_WORK="$TMP/p2scale" L4_SBM11_PACK="$BIN/l4sbm11-pack" "$HERE/phase2_scaling.sh" >"$TMP/p2scale.log" 2>&1 || rc=$?
  grep -E '^(ok|FAIL) ' "$TMP/p2scale.log" | sed 's/^/     /'
  if [ "$rc" -eq 0 ]; then record scaling phase2-n-2n-4n 0 "$(grep -c '^ok' "$TMP/p2scale.log") assertions hold"
  else record scaling phase2-n-2n-4n 1 "exit $rc: $(grep -E '^FAIL' "$TMP/p2scale.log" | head -1)"; fi
fi

echo "=== (m) RDF 1.2 triple terms (issue 792 item 1)"
G12SRC="$HERE/gate12/gate12.nq"
G12="$TMP/gate12"
rc=0
"$BIN/l4sbm11-pack" "$G12SRC" "$G12/gen" --workers 1 >"$TMP/g12pack.log" 2>&1 || rc=$?
[ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$G12" gen >"$TMP/g12act.log" 2>&1 || rc=$?; }
if [ "$rc" -ne 0 ]; then
  record rdf12 pack-activate 1 "exit $rc: $(tail -1 "$TMP/g12pack.log" "$TMP/g12act.log" 2>/dev/null | tr '\n' ' ')"
else
  record rdf12 pack-activate 0 "$(grep -o 'quads=[0-9]*' "$TMP/g12pack.log" | head -1); $(grep -o 'terms=[0-9]*' "$TMP/g12pack.log" | head -1)"
  # the same fixture with blocks of 2 rows, for --sip always and --threads 4
  "$BIN/l4sbm11-pack" "$G12SRC" "$G12/small" --workers 1 --block-rows 2 >"$TMP/g12small.log" 2>&1 || rc=$?
  for rq in "$HERE"/gate12/*.rq; do
    n="$(basename "$rq" .rq)"
    qb="file://$(realpath "$rq")"
    rrc=0
    timeout 120 "$BIN/l4factoidal" query "$G12SRC" --format nquads12 --sparql12 --query "$rq" \
      >"$TMP/m-$n.want" 2>/dev/null || rrc=$?
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$G12" --sparql12 --file "$rq" --base "$qb" >"$TMP/m-$n.got" 2>"$TMP/m-$n.err" || rc=$?
    if [ "$rc" -ne 0 ]; then record rdf12 "$n" 1 "exit $rc: $(tail -1 "$TMP/m-$n.err")"; continue; fi
    v="$(python3 -I "$HERE/compare_answers.py" "$TMP/m-$n.got" "$TMP/m-$n.want" "$rrc")"
    p="$(grep -o 'path=[a-z]*' "$TMP/m-$n.err")"
    want_path=path=ids; case $n in ref-*) want_path=path=reference ;; esac
    if [ "$p" != "$want_path" ]; then record rdf12 "$n" 1 "$p, expected $want_path"
    else case "$v" in equal*) record rdf12 "$n" 0 "$p; $v" ;; *) record rdf12 "$n" 1 "$p; $v" ;; esac
    fi
    # the reference fallback over the decoded quads
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$G12" --sparql12 --file "$rq" --base "$qb" --reference \
      >"$TMP/m-$n.fb" 2>/dev/null || rc=$?
    v="$(python3 -I "$HERE/compare_answers.py" "$TMP/m-$n.fb" "$TMP/m-$n.want" "$rrc")"
    case "$rc:$v" in 0:equal*) record rdf12 "$n--reference" 0 "$v" ;; *) record rdf12 "$n--reference" 1 "exit $rc; $v" ;; esac
    # the key printer against jsonOfTerm
    rc=0
    timeout 120 "$BIN/l4sbm11" query "$G12" --sparql12 --file "$rq" --base "$qb" --reference-render \
      >"$TMP/m-$n.rr" 2>/dev/null || rc=$?
    if [ "$rc" -eq 0 ] && cmp -s "$TMP/m-$n.got" "$TMP/m-$n.rr"; then record rdf12 "$n--render" 0 "byte-identical"
    else record rdf12 "$n--render" 1 "exit $rc or outputs differ"; fi
    # blocks of 2 rows, candidates into every join scan, 4 scan tasks
    case $n in ids-*)
      rc=0
      SBM11_MIN_RANGE_ROWS=0 timeout 120 "$BIN/l4sbm11" query "$G12/small" --sparql12 --file "$rq" --base "$qb" \
        --sip always --threads 4 >"$TMP/m-$n.small" 2>"$TMP/m-$n.smallerr" || rc=$?
      v="$(python3 -I "$HERE/compare_answers.py" "$TMP/m-$n.small" "$TMP/m-$n.want" "$rrc")"
      p="$(grep -o 'path=[a-z]*' "$TMP/m-$n.smallerr")"
      case "$rc:$p:$v" in 0:path=ids:equal*) record rdf12 "$n--small-blocks" 0 "$v" ;;
        *) record rdf12 "$n--small-blocks" 1 "exit $rc; $p; $v" ;; esac ;;
    esac
  done
  # dump equals canon of the source, as sets. `l4sbm11 canon` reads the source
  # through the source layer (RDF 1.2, https://github.com/danbri/factoidal/issues/837).
  # Until 2026-10-14 this case was an expected failure, because canon parsed
  # RDF 1.1 and refused the first triple term.
  rc=0
  "$BIN/l4sbm11" dump "$G12" 2>/dev/null | sort -u >"$TMP/g12dump.nq" || rc=$?
  crc=0
  "$BIN/l4sbm11" canon "$G12SRC" >"$TMP/g12canon.raw" 2>"$TMP/g12canon.err" || crc=$?
  sort -u "$TMP/g12canon.raw" >"$TMP/g12canon.nq"
  if [ "$rc" -eq 0 ] && [ "$crc" -eq 0 ] && [ -s "$TMP/g12dump.nq" ] && cmp -s "$TMP/g12dump.nq" "$TMP/g12canon.nq"; then
    record rdf12 dump-equals-canon 0 "$(wc -l <"$TMP/g12dump.nq") quads"
  else
    record rdf12 dump-equals-canon 1 "exit $rc/$crc; dump $(wc -l <"$TMP/g12dump.nq"), canon $(wc -l <"$TMP/g12canon.nq") lines; $(head -c 160 "$TMP/g12canon.err")"
  fi
  # dump equals the reference parser's canonical N-Quads of the source, as
  # sets (an implementation that shares no code with the packer's reader)
  rc=0
  "$BIN/l4factoidal" parse "$G12SRC" --format nquads12 --out nquads 2>/dev/null | grep -v '^$' | sort -u >"$TMP/g12ref.nq" || rc=$?
  if [ "$rc" -eq 0 ] && [ -s "$TMP/g12ref.nq" ] && cmp -s "$TMP/g12dump.nq" "$TMP/g12ref.nq"; then
    record rdf12 dump-equals-reference-parse 0 "$(wc -l <"$TMP/g12ref.nq") quads"
  else
    record rdf12 dump-equals-reference-parse 1 "exit $rc; dump $(wc -l <"$TMP/g12dump.nq"), reference $(wc -l <"$TMP/g12ref.nq") lines"
  fi
  # the dictionary alone: every key decodes to a term whose key is the same
  # bytes, every term of the source is found
  rc=0
  "$BIN/l4sbm11-dict-pack" "$G12SRC" "$TMP/g12dict" >/dev/null 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11-dict-pack" --check "$G12SRC" "$TMP/g12dict" >"$TMP/g12check.log" 2>&1 || rc=$?; }
  if [ "$rc" -eq 0 ] && grep -q 'failures=0' "$TMP/g12check.log"; then
    record rdf12 dict-check 0 "$(grep -o 'keys=[0-9]*' "$TMP/g12check.log" | head -1); failures=0"
  else record rdf12 dict-check 1 "exit $rc: $(grep 'FAIL' "$TMP/g12check.log" | head -1)"; fi
  # compaction over a base with triple terms re-keys their tag-9 ids
  # (Sbm11Compact.kindOf): after one update, the compacted generation is
  # byte-identical to a fresh pack of the updated quads
  M="$TMP/g12delta"
  mkdir -p "$M"
  cp "$G12SRC" "$M/final.nq"
  echo '<http://ex.org/z> <http://ex.org/name> "Zed" .' >>"$M/final.nq"
  rc=0
  "$BIN/l4sbm11-pack" "$G12SRC" "$M/col/gen" --workers 1 >/dev/null 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$M/col" gen >/dev/null 2>&1 || rc=$?; }
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" update "$M/col" 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Zed" }' >"$M/upd.log" 2>&1 || rc=$?; }
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" compact "$M/col" "$M/col/gen2" >"$M/compact.log" 2>&1 || rc=$?; }
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11-pack" "$M/final.nq" "$M/fresh" --workers 1 >/dev/null 2>&1 || rc=$?; }
  if [ "$rc" -ne 0 ]; then record rdf12 compact-equals-fresh-pack 1 "exit $rc: $(tail -1 "$M/upd.log" "$M/compact.log" 2>/dev/null | tr '\n' ' ')"
  else
    v="$(same_artifacts "$M/col/gen2" "$M/fresh")"; c=$?
    record rdf12 compact-equals-fresh-pack "$c" "$v"
    # the reference route decodes triple terms to terms and the packer keys them again
    cqrc=0
    "$BIN/l4sbm11" compact "$M/col" "$M/viaq" --via-quads >"$M/compactq.log" 2>&1 || cqrc=$?
    if [ "$cqrc" -ne 0 ]; then record rdf12 compact-via-quads 1 "exit $cqrc: $(tail -1 "$M/compactq.log")"
    else
      v="$(same_artifacts "$M/viaq" "$M/col/gen2")"; c=$?
      record rdf12 compact-via-quads-equals-default "$c" "$v"
    fi
  fi
  # SPARQL 1.2 Update through the delta log (https://github.com/danbri/factoidal/issues/792
  # item 1, the update part). A fresh generation of the fixture takes a plain
  # update (the log is DLOG version 1), then the three requests of
  # tests/sbm11/gate12/update/ with --sparql12: u1 inserts triple terms (one
  # the base holds, new ones, one nested three deep, one in a named graph) and
  # directional literals, and the log gets version 2 in place; u2 deletes
  # triple-term quads of the base and of u1; u3 is an INSERT DATA and a DELETE
  # DATA in one request. The reference is `l4factoidal update --sparql12` of
  # the same requests over the source. After each request every
  # gate12/update/*.rq query is answered by `l4sbm11 query --sparql12` on its
  # path (ids-* on path=ids, ref-* on path=reference) and by --reference,
  # equal as multisets to `l4factoidal query --sparql12` over the reference
  # state; after u3 the 46 gate12/*.rq queries too. Then compaction: the dump
  # of the compacted generation equals the reference state, and the compacted
  # generation is byte-identical to a fresh pack of it. Until 2026-10-14 this
  # part held the expected failure xfail-update-triple-term (refused: SPARQL
  # 1.1 Update grammar, no triple-term form in the DLOG term codec).
  U="$TMP/g12upd"
  UD="$HERE/gate12/update"
  mkdir -p "$U"
  cp "$G12SRC" "$U/state.nq"
  rc=0
  "$BIN/l4sbm11-pack" "$G12SRC" "$U/col/gen" --workers 1 >/dev/null 2>&1 || rc=$?
  [ "$rc" -eq 0 ] && { "$BIN/l4sbm11" activate "$U/col" gen >/dev/null 2>&1 || rc=$?; }
  upd_step() { # upd_step <label> <update file> [--sparql12]: the store and the reference state
    local urc=0 rrc=0
    "$BIN/l4sbm11" update "$U/col" --file "$2" ${3:+"$3"} >"$U/$1.upd" 2>&1 || urc=$?
    "$BIN/l4factoidal" update "$U/state.nq" --format nquads12 --update "$2" ${3:+"$3"} \
      >"$U/$1.nq" 2>"$U/$1.referr" || rrc=$?
    if [ "$urc" -eq 0 ] && [ "$rrc" -eq 0 ] && [ -s "$U/$1.nq" ]; then
      cp "$U/$1.nq" "$U/state.nq"
      record rdf12 "update-$1" 0 "$(grep -o 'seq=[0-9]* epoch=[0-9]* ops=[0-9]*' "$U/$1.upd"); $(grep -o 'log-version=.*' "$U/$1.upd")"
    else
      record rdf12 "update-$1" 1 "exit $urc (reference $rrc): $(tail -1 "$U/$1.upd") $(head -c 160 "$U/$1.referr")"
    fi
  }
  upd_queries() { # upd_queries <label> <query files...>: each query against the reference state
    local label="$1" rq n qb rrc qrc frc v vf p want_path
    shift
    for rq in "$@"; do
      n="$(basename "$rq" .rq)"
      qb="file://$(realpath "$rq")"
      rrc=0
      timeout 120 "$BIN/l4factoidal" query "$U/state.nq" --format nquads12 --sparql12 --query "$rq" \
        >"$U/w.json" 2>/dev/null || rrc=$?
      qrc=0
      timeout 120 "$BIN/l4sbm11" query "$U/col" --sparql12 --file "$rq" --base "$qb" \
        >"$U/g.json" 2>"$U/g.err" || qrc=$?
      v="$(python3 -I "$HERE/compare_answers.py" "$U/g.json" "$U/w.json" "$rrc")"
      p="$(grep -o 'path=[a-z]*' "$U/g.err")"
      want_path=path=ids; case $n in ref-*) want_path=path=reference ;; esac
      frc=0
      timeout 120 "$BIN/l4sbm11" query "$U/col" --sparql12 --file "$rq" --base "$qb" --reference \
        >"$U/f.json" 2>/dev/null || frc=$?
      vf="$(python3 -I "$HERE/compare_answers.py" "$U/f.json" "$U/w.json" "$rrc")"
      if [ "$qrc" -eq 0 ] && [ "$p" = "$want_path" ] && [ "$frc" -eq 0 ]; then
        case "$v|$vf" in
          equal*"|"equal*) record rdf12 "$label-$n" 0 "$p; $v; --reference equal" ;;
          *) record rdf12 "$label-$n" 1 "$p; $v; --reference: $vf" ;;
        esac
      else
        record rdf12 "$label-$n" 1 "exit $qrc, $p (want $want_path), --reference exit $frc: $(tail -1 "$U/g.err")"
      fi
    done
  }
  if [ "$rc" -ne 0 ]; then
    record rdf12 update-setup 1 "pack or activate failed, exit $rc"
  else
    # a plain update: the log is version 1, the bytes of the version 1 writer
    printf '%s\n' 'INSERT DATA { <http://ex.org/z> <http://ex.org/name> "Zed" }' >"$U/u0.ru"
    upd_step u0 "$U/u0.ru"
    "$BIN/l4block-delta-log" "$U/col" --inspect >"$U/i0.log" 2>&1
    if grep -q 'version=1 committed-batches=1' "$U/i0.log" && grep -q 'log-version=1' "$U/u0.upd"; then
      record rdf12 update-log-version-1 0 "$(grep -o 'version=1 committed-batches=1' "$U/i0.log")"
    else record rdf12 update-log-version-1 1 "$(cat "$U/i0.log" "$U/u0.upd" | tr '\n' ' ')"; fi
    for k in 1 2 3; do
      upd_step "u$k" "$UD/u$k.ru" --sparql12
      if [ "$k" -eq 1 ]; then
        # the first batch with an RDF 1.2 term sets the header version to 2
        "$BIN/l4block-delta-log" "$U/col" --inspect >"$U/i1.log" 2>&1
        if grep -q 'version=2 committed-batches=2' "$U/i1.log" && grep -q 'log-version=2 (set from 1)' "$U/u1.upd"; then
          record rdf12 update-log-version-2 0 "set from 1 in place; $(grep -o 'version=2 committed-batches=2' "$U/i1.log")"
        else record rdf12 update-log-version-2 1 "$(cat "$U/i1.log" "$U/u1.upd" | tr '\n' ' ')"; fi
      fi
      if [ "$k" -lt 3 ]; then upd_queries "u$k" "$UD"/*.rq
      else upd_queries "u$k" "$UD"/*.rq "$HERE"/gate12/*.rq; fi
    done
    # the former stage 5 limits (https://github.com/danbri/factoidal/issues/849 and
    # https://github.com/danbri/factoidal/issues/850): a blank node inside a nested triple term in INSERT DATA (u4),
    # and DELETE WHERE with a triple-term pattern that has a variable (u5), are applied and equal the reference state
    printf '%s\n' 'INSERT DATA { <http://ex.org/k> <http://ex.org/says> <<( <http://ex.org/s> <http://ex.org/p> <<( _:x <http://ex.org/q> "1" )>> )>> }' >"$U/u4.ru"
    printf '%s\n' 'DELETE WHERE { ?s <http://ex.org/says> <<( <http://ex.org/s> <http://ex.org/p> ?o )>> }' >"$U/u5.ru"
    for k in 4 5; do
      upd_step "u$k" "$U/u$k.ru" --sparql12
      upd_queries "u$k" "$UD"/*.rq
    done
    # refusals that stay: a blank node inside a triple term of DELETE DATA is a SPARQL 1.2 syntax error, and a
    # triple term without --sparql12 is a SPARQL 1.1 parse error; neither changes the log
    cp "$U/col/gen/deltas.dlog" "$U/before-refusals.dlog"
    r=0; "$BIN/l4sbm11" update "$U/col" --sparql12 \
      'DELETE DATA { <http://ex.org/k> <http://ex.org/says> <<( _:x <http://ex.org/q> "1" )>> }' >"$U/r2.log" 2>&1 || r=$?
    if [ "$r" -eq 1 ] && grep -q 'DELETE DATA must not contain blank nodes' "$U/r2.log"; then record rdf12 refuse-delete-nested-bnode 0 "parse error, as SPARQL 1.2 requires"
    else record rdf12 refuse-delete-nested-bnode 1 "exit $r: $(tail -1 "$U/r2.log")"; fi
    r=0; "$BIN/l4sbm11" update "$U/col" \
      'INSERT DATA { <http://ex.org/k> <http://ex.org/says> <<( <http://ex.org/s> <http://ex.org/p> "1" )>> }' >"$U/r4.log" 2>&1 || r=$?
    if [ "$r" -eq 1 ] && grep -q 'parse error' "$U/r4.log"; then record rdf12 refuse-triple-term-sparql11 0 "parse error without --sparql12"
    else record rdf12 refuse-triple-term-sparql11 1 "exit $r: $(tail -1 "$U/r4.log")"; fi
    if cmp -s "$U/col/gen/deltas.dlog" "$U/before-refusals.dlog"; then record rdf12 refusals-leave-log 0 "the log bytes did not change"
    else record rdf12 refusals-leave-log 1 "a refused update changed the log"; fi
    # compaction: the dump equals the reference state; byte-identical to a fresh pack of it
    rc=0
    "$BIN/l4sbm11" compact "$U/col" "$U/col/gen2" >"$U/compact.log" 2>&1 || rc=$?
    [ "$rc" -eq 0 ] && { "$BIN/l4sbm11-pack" "$U/state.nq" "$U/fresh" --workers 1 >/dev/null 2>&1 || rc=$?; }
    if [ "$rc" -ne 0 ]; then record rdf12 update-compact 1 "exit $rc: $(tail -1 "$U/compact.log")"
    else
      "$BIN/l4sbm11" dump "$U/col/gen2" 2>/dev/null | sort -u >"$U/dump.nq"
      grep -v '^$' "$U/state.nq" | sort -u >"$U/want.nq"
      if [ -s "$U/dump.nq" ] && cmp -s "$U/dump.nq" "$U/want.nq"; then
        record rdf12 update-compact-dump 0 "$(wc -l <"$U/dump.nq") quads equal to the reference state"
      else
        record rdf12 update-compact-dump 1 "dump $(wc -l <"$U/dump.nq"), reference $(wc -l <"$U/want.nq") lines; $(diff "$U/dump.nq" "$U/want.nq" | head -3 | tr '\n' ' ')"
      fi
      v="$(same_artifacts "$U/col/gen2" "$U/fresh")"; c=$?
      record rdf12 update-compact-equals-fresh-pack "$c" "$v"
    fi
  fi
fi

echo "=== (n) layering: the store names no syntax module (issue 837)"
rc=0
out="$(python3 -I "$HERE/storage_layering.py" "$ROOT/formal/lean4/L4Factoidal/Storage" 2>&1)" || rc=$?
if [ "$rc" -eq 0 ]; then record layering storage-no-syntax 0 "$(printf '%s' "$out" | tail -1)"
else record layering storage-no-syntax 1 "exit $rc: $(printf '%s' "$out" | head -3 | tr '\n' ' ')"; fi

echo "=== (o) syntax independence (issue 837)"
rc=0
L4_BIN_DIR="$BIN" bash "$HERE/syntax_independence.sh" >"$TMP/syntax.log" 2>&1 || rc=$?
grep -vE '^(syntax independence:|$)' "$TMP/syntax.log" | sed 's/^/     /'
sum="$(grep '^syntax independence:' "$TMP/syntax.log")"
if [ -n "$sum" ]; then
  sp="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail, \([0-9]*\) expected-fail.*/\1/p')"
  sf="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail, \([0-9]*\) expected-fail.*/\2/p')"
  sx="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail, \([0-9]*\) expected-fail.*/\3/p')"
  PASS=$((PASS + sp)); FAIL=$((FAIL + sf)); XFAILS=$((XFAILS + sx))
  echo "     $sum"
else record syntax independence 1 "exit $rc: no summary line"; fi

# add_script_counts PART SCRIPT SUMMARY-PREFIX: run SCRIPT, show its log, and add the
# counts of its summary line ("PREFIX: N pass, M fail, K expected-fail (out of T)").
add_script_counts() {
  local part="$1" script="$2" prefix="$3" rc=0 sum sp sf sx log="$TMP/$1.log"
  L4_BIN_DIR="$BIN" bash "$HERE/$script" >"$log" 2>&1 || rc=$?
  grep -vE "^($prefix:|\$)" "$log" | sed 's/^/     /'
  sum="$(grep "^$prefix:" "$log")"
  if [ -n "$sum" ]; then
    sp="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail, \([0-9]*\) expected-fail.*/\1/p')"
    sf="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail, \([0-9]*\) expected-fail.*/\2/p')"
    sx="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail, \([0-9]*\) expected-fail.*/\3/p')"
    PASS=$((PASS + sp)); FAIL=$((FAIL + sf)); XFAILS=$((XFAILS + sx))
    echo "     $sum"
    # a script that exits non-zero with no failed case is a failure of its own
    if [ "$rc" -ne 0 ] && [ "$sf" -eq 0 ]; then record "$part" "$script-exit" 1 "exit $rc with no failed case"; fi
  else record "$part" "$script" 1 "exit $rc: no summary line"; fi
}

echo "=== (p) the W3C RDF tests through the store (issue 837 item 5)"
add_script_counts w3c w3c_roundtrip.sh "w3c round trip"

echo "=== (q) export: the store written in each syntax, packed again (issue 837 item 6)"
add_script_counts export export_roundtrip.sh "export round trip"

echo "=== (r) update with a WHERE clause, graph management and fresh blank nodes (issues 849 and 850)"
add_script_counts update update_where.sh "update where"

echo "=== (s) the W3C SPARQL 1.1 Update evaluation tests through the store (issue 849 item 3)"
add_script_counts w3c-update w3c_update.sh "w3c update"

echo "=== (t) grouped aggregates on ids (issue 825)"
add_script_counts agg-ids agg_ids.sh "agg ids"

echo "=== (u) the packer takes quads from any producer (issue 866)"
add_script_counts quad-source quad_source.sh "quad source"

echo "=== (v) every named graph on the query paths and the export (issues 855 and 856)"
add_script_counts graphs named_graphs.sh "named graphs"

echo "=== (w) the temporary disk of the exact permutation check (issue 810)"
add_script_counts permdisk perm_check_disk.sh "perm check disk"

echo "=== (x) the compiled scan differential and the counting reference (issue 799, KR 1.2)"
# The scan decodes frames with FrameWords.decodeWordsF, which reaches the extern
# Prim.Bytes.pushU64LE; the build-time interpreter cannot run it, so the old-scan
# comparison of ScanFoldTests and the countChunk comparison run here.
if [ -x "$BIN/l4scanfold-test" ]; then
  rc=0; out="$("$BIN/l4scanfold-test" 2>&1)" || rc=$?
  record scanfold l4scanfold-test "$rc" "$out"
else record scanfold l4scanfold-test 1 "missing $BIN/l4scanfold-test (lake build l4scanfold-test)"; fi

echo
echo "sbm11 stages 4 and 5: $PASS pass, $FAIL fail, $XFAILS expected-fail (out of $((PASS + FAIL + XFAILS)))"
[ "$FAIL" -eq 0 ]
