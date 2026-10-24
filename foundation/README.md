# The FOUNDATION layer (version 0)

`manifest.toml` names the Lean modules under `formal/lean4/L4Factoidal/`
that are the specification layer of Factoidal. Every other L4Factoidal
module is an implementation (a store, an index, a planner, a codec, a fast
path, a wasm op, a harness) or a proof about one. Issue:
<https://github.com/danbri/factoidal/issues/975>, "Architecture acceptance",
item 1.

**This is version 0.** The module choice and the citations were made on
2026-10-24 by reading the Lean sources. They are not owner decisions and
they are not reviewed by W3C experts. Owner steer, 2026-10-24, verbatim:
"the details matter less than that we can do it, and that the human experts
can refine it later." The full steer is in the header of `manifest.toml`.

## Levels

| Level | Contents |
|---|---|
| 0 | The RDF and RDFS model: terms, IRIs and IRI resolution, literals and the XSD datatypes that RDF uses, graphs, datasets with named graphs, RDF Semantics and entailment. |
| 1 | SPARQL 1.1 (algebra, semantics, update, entailment regimes, the extension functions text and geo), the XPath functions and operators, OWL 2 (RL, RDF-Based, Direct), RIF, SHACL, ShEx, RDFC-1.0, and the evidence (FPP0) and stage-contract types. |
| 2 | Concrete syntaxes: XML, XPath 1.0, JSON, the RDF syntaxes, the SPARQL grammar and result formats, the OWL, RIF and ShEx syntaxes. |
| 3 | Mapping languages built on levels 0 to 2: CSVW, RML, JSON-LD. |

A module of level k may import foundation modules of level k or lower,
and Lean core, `Std` and Mathlib. It may not import an implementation
module or a module of a higher level.

## The gate

```
python3 -I tools/foundation-gate.py            # the gate on this tree
python3 -I tests/foundation/test_foundation_gate.py   # the gate's own tests
```

Both run in `tests/dataflow/run.sh`. The gate reads the manifest and the
leading `import` lines of every `.lean` file on every run (no Lean build is
needed). It fails when:

1. a module in the manifest has no file;
2. a foundation module imports a module outside the foundation (`impl`);
3. a level-k module imports a module of a higher level (`level`);
4. a violation is not in `allow-imports.txt`;
5. `allow-imports.txt` has an entry that is no longer a violation, an
   entry with no reason, or a number of entries different from its
   `# max-entries: N` header;
6. the walk finds no `.lean` files.

Each violation prints as `file:line: kind: FROM -> TO`.
`--verbose` also prints the allowed violations.

## The ratchet

`allow-imports.txt` lists today's violations, one per line, each with a
reason:

```
L4Factoidal.SPARQL.Query -> L4Factoidal.SPARQL.ExistsIndex  # impl: EXISTS fast path ...; split
```

The list may only shrink. When you remove a violation from the Lean source,
remove its line and lower `max-entries` in the same commit; the gate fails
on a stale line. Do not add a line to make a new import pass. If a new
edge is necessary, the PR must say why, and the reviewer sees the change to
`max-entries`.

## Adding a module

1. Add a `[[module]]` entry to `manifest.toml` with `name`, `level` and
   `spec` (the W3C document and section it transcribes; for a module with
   no W3C document, say so and link the issue).
2. Run the gate. Every L4Factoidal import of the new module must be a
   foundation module of the same or a lower level. If it is not, move the
   dependency into the foundation (when it is a specification), or split
   the module so that the specification part does not import the
   implementation.
3. Adding a module can make an allow-list line stale (its target is now
   in the foundation). Remove that line and lower `max-entries`.

Removing a module from the manifest is a refinement of version 0; state the
reason in the PR.

## Entry points (issue 975, item 3)

`tools/entrypoint-gate.py` enumerates, from the tree on every run, every
shipped entry point:

- `npm:<subpath>#<name>`: each named export of each `exports` subpath of
  `npm/factoidal/package.json` (ES module `export` forms and CommonJS
  `module.exports`); `npm:<subpath>` for a subpath that is not a script.
- `wasm:<op>`: each op name of the Lean dispatch (the `...OpNames` lists of
  `formal/lean4/Wasm/*.lean` and `Wasm/Ops/*.lean`, and the `| "op" =>`
  arms of `Wasm/Dispatch.lean` and `Wasm/CoreDispatch.lean`).
- `cli:<command>`: each key of `COMMANDS` in `npm/factoidal/bin/factoidal.mjs`.

Each entry point must be one of:

1. an `[[entry]]` of `entrypoints.toml`: `stages` names registry stages
   (from `docs/dataflow-inventory.md`, the `stage` cell, or the `area` cell
   when the registry entry has no declaration), none with status `missing`;
   `covers` is `whole` or `part` (the entry also runs steps no stage
   covers; the `note` names them and the file where the op body is);
2. a `[[nonstage]]` of `entrypoints.toml` with a reason (reflection ops,
   version strings, metadata files);
3. a literal constant or an `Error` subclass (the gate finds these);
4. a line of `unbound-entrypoints.txt`.

`unbound-entrypoints.txt` is a ratchet like `allow-imports.txt`: the gate
fails when a new entry point is not mapped, when a line names an entry that
no longer exists or is now mapped, or when the count differs from
`max-entries`. When you bind an entry point, move it from the unbound list to
`entrypoints.toml` and lower `max-entries` in the same commit.

The bound status of an entry is the weakest status of its stages
(`tested` < `assumed` < `proved`).

## Named assumptions (issue 975, items 2 and 4)

The interface types carry their contract as fields. `RdfReader`
(`formal/lean4/L4Factoidal/Dataflow/Reader.lean`) has no assumption field.
`LawfulStore` and `LawfulDataset` (`Dataflow/Store.lean`), the data-access
interface, have the field `assumptions : List Assumption`: the assumptions
the law rests on, each with a name from `inductive AssumptionName`. The query
ops, the dataset handles, the served view, the CLI and the harness query tools
reach the backend evaluator only through these types.

```
python3 -I tools/assumption-gate.py                      # the gate on this tree
python3 -I tests/foundation/test_assumption_gate.py      # the gate's own tests
```

Both run in `tests/dataflow/run.sh`. `assumptions.txt` has one line per
constructor of `AssumptionName`: the name, `uses=N` (the places in
`formal/lean4` that build an assumption of that name) and the reason it is not
proved. The gate fails when a count in the tree differs from its line, when a
constructor has no line, when the number of lines differs from
`# max-entries: N`, or when a file under `formal/lean4/Wasm` or
`formal/lean4/Harness` calls the backend evaluator over a bare
`DatasetBackend` (`runSelectQueryBackendDataset`, `runAskQueryBackendDataset`,
`evalPatternBackend`, `evalBgpBackend`, `indexedDatasetBackend`). A new use of
an assumption therefore changes `assumptions.txt` in the same PR, with a reason.
