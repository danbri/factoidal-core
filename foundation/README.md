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
