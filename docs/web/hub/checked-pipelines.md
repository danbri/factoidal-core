---
title: Checked pipelines
description: Compose readers, reasoners, the SPARQL evaluator and writers as nodes; each step records its status and contract, and the result lists what the answer depends on.
layout: hub.njk
tests: tests/hub/hub_checked-pipelines_test.mjs
---

# Checked pipelines

[Hub](../) · stages, nodes, evidence, assumptions

The cells on this page run `@factoidal/core` {{ factoidalRelease.version }}
from the npm registry ([npm]({{ factoidalRelease.npmUrl }}), loaded from
`{{ factoidalRelease.base }}`).

Each component of the package (a reader, a reasoner, the SPARQL evaluator,
a writer, a validator) is registered with a status and a contract. The
status is one of `proved` (a Lean 4 theorem states the contract against
the W3C specification), `tested` (a test suite, no theorem), `assumed` (the
contract is a named assumption) or `missing` (no contract and no suite).

`node(name, params)` makes a node for one component, `pipe(...)` composes
nodes left to right, and `run(pipeline, input)` runs it. A value on a wire is
`{graph, evidence}`; each node adds one evidence record. `pipe()` asks the
engine's op `pipelineCheck` whether each node's output type is the next
node's input type, and `run()` refuses a pipeline that is not well typed
(see the last section). Status:
[issue 975](https://github.com/danbri/factoidal/issues/975) (component
contracts) and [issue 1002](https://github.com/danbri/factoidal/issues/1002)
(dataflow and explanations).

```observable-js
release = Factoidal.version
```

## Is a description entailed?

The sources say that Alice works for Acme, that the domain of `worksFor` is
`Employee`, and that `Employee` is a subclass of `Person`. The description
says that something is a `Person` and works for Acme. Its blank node `_:x` is
a variable.

```observable-js
sources = `@prefix ex: <http://example.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
ex:alice ex:worksFor ex:acme .
ex:worksFor rdfs:domain ex:Employee .
ex:Employee rdfs:subClassOf ex:Person .`
```

```observable-js
description = `@prefix ex: <http://example.org/> .
_:x a ex:Person . _:x ex:worksFor ex:acme .`
```

The pipeline reads Turtle, computes the RDFS closure, and asks the
explanation stage whether the description is entailed:

```observable-js
entailedRun = {
  const p = Factoidal.pipe(
    await Factoidal.node('turtleDocumentReader'),
    await Factoidal.node('rdfsReasoner'),
    await Factoidal.node('rdfsExplainGraphStage', { description }),
  );
  return Factoidal.run(p, sources);
}
```

One evidence record per node: the stage, its status, its contract (a Lean
declaration), and whether the step is checked (status `proved`).

```observable-js
entailedEvidence = {
  const rows = entailedRun.evidence.map((e) => ({ stage: e.stage, status: e.status, contract: e.contract, checked: e.checked }));
  return pretty(rows);
}
```

The verdict, the blank-node mapping, and the two lists of assumptions: the
verdict's own list and the union over the nodes of the run.

```observable-js
entailedVerdict = {
  const a = entailedRun.evidence[2].artefact;
  return ({
    entailed: a.entailed,
    mapping: a.bundle.mapping.map((m) => `_:${m.bnode} -> ${m.term}`).join(', '),
    verdictAssumptions: a.assumptions,
    runAssumptions: entailedRun.assumptions,
    proved: entailedRun.proved,
  });
}
```

`entailed: true` means the graph checker accepted the bundle (the sources,
the description, the mapping and the derivation steps). Both lists are
empty.

The explanation stage can also read the parsed sources directly, without
the reasoner. The derivation then has the RDFS rules in it: `rdfs2` (domain)
derives that Alice is an `Employee`, and `rdfs9` (subclass) derives that she
is a `Person`.

```observable-js
derivation = {
  const p = Factoidal.pipe(
    await Factoidal.node('turtleDocumentReader'),
    await Factoidal.node('rdfsExplainGraphStage', { description }),
  );
  const r = await Factoidal.run(p, sources);
  const short = (t) => t.replace(/<http:\/\/example\.org\/([^>]*)>/g, 'ex:$1')
    .replace(/<http:\/\/www\.w3\.org\/1999\/02\/22-rdf-syntax-ns#type>/g, 'a')
    .replace(/<http:\/\/www\.w3\.org\/2000\/01\/rdf-schema#([^>]*)>/g, 'rdfs:$1').trim();
  const steps = r.evidence[1].artefact.bundle.steps;
  return pretty(steps.map((s, i) => ({ step: i, rule: s.rule, conclusion: short(s.conclusion), premises: s.premises.join(' ') })));
}
```

## A description that is not entailed

Nothing in the sources says that anyone works for Globex.

```observable-js
notEntailedRun = {
  const p = Factoidal.pipe(
    await Factoidal.node('turtleDocumentReader'),
    await Factoidal.node('rdfsReasoner'),
    await Factoidal.node('rdfsExplainGraphStage', { description: `@prefix ex: <http://example.org/> .
_:x ex:worksFor ex:globex .` }),
  );
  return Factoidal.run(p, sources);
}
```

```observable-js
notEntailedVerdict = {
  const a = notEntailedRun.evidence[2].artefact;
  return ({
    entailed: a.entailed,
    rejection: a.rejection.kind,
    triple: a.rejection.triple.trim(),
    verdictAssumptions: a.assumptions,
    runAssumptions: notEntailedRun.assumptions,
  });
}
```

The rejection is `noMatch`: the RDFS closure has no instance of the triple.
A "yes" is a checked derivation, so it needs no assumption. A "no" says that
no derivation exists, and that holds only if the closure the engine computed
holds every RDFS consequence; that completeness is not proved yet, so the
verdict names it as an assumption.

In 0.15.0 the run's own `assumptions` list stays empty here: it is the union
of the components' registered assumptions, and the registry lists none for
`rdfsReasoner` or `rdfsExplainGraphStage`. Read the verdict's list with the
verdict.

## A step that is not proved

The Turtle writer has the status `assumed`: its contract (a round trip of
the written text) is the named assumption `TurtleWriterRoundTrip`. A run
through it answers `proved: false` and names the step in `uncheckedSteps`.

```observable-js
writerRun = {
  const p = Factoidal.pipe(await Factoidal.node('turtleDocumentReader'), await Factoidal.node('turtleDocumentWriter'));
  const r = await Factoidal.run(p, sources, { unchecked: true });
  const w = r.evidence[1];
  return ({ proved: r.proved, uncheckedSteps: r.uncheckedSteps, status: w.status, contract: w.contract, reason: w.reason, text: w.artefact.text });
}
```

`{ unchecked: true }` is the opt-in on `run`. With it, a step that is not
checked carries `unchecked: true` and a `reason`. In 0.15.0 a run without the
opt-in also runs a well-typed pipeline with a `tested` or `assumed` step (the
result still says `proved: false`). It refuses a `missing` stage, and a
pipeline that is not well typed (next section):

```observable-js
missingStage = {
  try {
    const p = Factoidal.pipe(await Factoidal.node('turtleDocumentReader'), await Factoidal.node('JSON-LD expansion, compaction, framing'));
    await Factoidal.run(p, sources);
    return 'ran';
  } catch (e) {
    return ({ code: e.code, message: e.message });
  }
}
```

## A pipeline that is not well typed

The Turtle writer gives text, and the RDFS reasoner reads a graph. `pipe()`
reports the type check as `wellTyped` and `check`: the mismatch is at the
wire between node 1 (the writer) and node 2 (the reasoner). The check is
computed in Lean from the stage registry; the theorem
`Pipeline.guarantee_sound` gives the guarantee of every well-typed pipeline.

```observable-js
illTyped = Factoidal.pipe(
  await Factoidal.node('turtleDocumentReader'),
  await Factoidal.node('turtleDocumentWriter'),
  await Factoidal.node('rdfsReasoner'),
)
```

```observable-js
illTypedCheck = ({
  wellTyped: illTyped.wellTyped,
  mismatch: illTyped.check.mismatch,
  theorem: illTyped.check.contract.theorem,
})
```

`run()` refuses it:

```observable-js
illTypedRun = {
  try {
    await Factoidal.run(illTyped, sources);
    return 'ran';
  } catch (e) {
    return ({ code: e.code, message: e.message });
  }
}
```

With `{ unchecked: true }` it runs, and the result says `wellTyped: false`
and `proved: false`:

```observable-js
illTypedUnchecked = {
  const r = await Factoidal.run(illTyped, sources, { unchecked: true });
  return ({ wellTyped: r.wellTyped, proved: r.proved, uncheckedSteps: r.uncheckedSteps });
}
```

## What is proved and what is not

`stages()` lists the registry of the Lean library, one entry per component.
`bound` is true when this package has a function that runs it as a node.

```observable-js
registry = Factoidal.stages()
```

```observable-js
statusCounts = {
  const counts = { proved: 0, tested: 0, assumed: 0, missing: 0 };
  for (const s of registry) counts[s.status] += 1;
  return ({ entries: registry.length, ...counts });
}
```

The components you can use as nodes:

```observable-js
boundStages = {
  const rows = registry.filter((s) => s.bound).map((s) => ({
    name: s.name, kind: s.kind, status: s.status,
    assumptions: s.assumptions.map((a) => a.split('.').pop()).join(', '),
  }));
  return pretty(rows);
}
```

The entries with status `missing` are areas with no contract and no test
suite in the registry yet:

```observable-js
missingAreas = {
  const rows = registry.filter((s) => s.status === 'missing').map((s) => ({ area: s.name }));
  return pretty(rows);
}
```

## A SPARQL step

`shippedEvaluator` takes `{ query }`. Its contract `EvalContract` states that
the answer agrees with the SPARQL 1.1 semantics. Here it reads the RDFS
closure, so Alice is a `Person`:

```observable-js
sparqlRun = {
  const p = Factoidal.pipe(
    await Factoidal.node('turtleDocumentReader'),
    await Factoidal.node('rdfsReasoner'),
    await Factoidal.node('shippedEvaluator', { query: 'PREFIX ex: <http://example.org/> SELECT ?who WHERE { ?who a ex:Person }' }),
  );
  return Factoidal.run(p, sources);
}
```

```observable-js
sparqlResult = {
  const e = sparqlRun.evidence[2];
  return ({
    stage: e.stage, status: e.status, contract: e.contract,
    who: e.artefact.answer.map((row) => row.get('who').value),
    proved: sparqlRun.proved, assumptions: sparqlRun.assumptions,
  });
}
```
