---
title: "Ethereum bytecode → WASM → SPARQL"
description: "Editable Factoidal queries invoking WASM generated from EVM bytecode: a pure uint256 predicate, a five-condition policy, source mutation and provenance."
layout: hub.njk
evmWasmSparqlDemo: true
tests: tests/hub/hub_ethereum_wasm_sparql_test.mjs
---

# Ethereum bytecode → WASM → SPARQL

[Hub](../) · [SPARQL](../sparql/) · [Compiler source](https://github.com/danbri/factoidal-core/tree/main/labs/ethereum-wasm-sparql)

**Edit a cell and press Run.** These examples compile real, hand-authored EVM runtime bytes to import-free WebAssembly, instantiate it in your browser, register its export using Factoidal's SPARQL 1.1 `17.6 extension-function API, and query hypothetical RDF data. No node, wallet or Ethereum API is contacted.

All examples are **pure functions**. They are **not** interpretations of deployed contracts or authenticated current chain state. The EVM→WASM translation is restricted and *differentially tested, not formally proved*.

## 1. From EVM bytecode to an executable SPARQL function

The first program computes `balance ≥ amount`, reading two ABI-encoded uint256 words from calldata and returning a 32-byte ABI Boolean.

```observable-js
simpleEvmHex = "6004356024359010155f5260205ff3"
```

Decode the actual EVM stack operations; don't replace them with a handwritten JavaScript comparison.

```observable-js
simpleCompiler = EvmCompiler.compileEvmToWasm256(simpleEvmHex)
```

```observable-js
simpleDisassembly = pretty(simpleCompiler.operations.map(op => ({
  pc: op.pc, opcode: op.name, operand: op.offset ?? op.word ?? ""
})))
```

Exactly as in the Hub's [`wasmAdd` example](../sparql/), instantiate WASM and register a callable function IRI. Here, **the WASM bytes were generated from the EVM program**. Two 256-bit arguments are carried as eight unsigned 64-bit limbs.

```observable-js
simpleWasm = {
  const { instance, module } = await WebAssembly.instantiate(simpleCompiler.bytes);
  if (WebAssembly.Module.imports(module).length) throw Error("Unexpected WASM imports");
  await Factoidal.registerExtensionFunction(
    "urn:factoidal:ethereum-wasm#canTransfer256",
    args => {
      if (args.length !== 2) throw TypeError("Expected balance and amount");
      return instance.exports.evaluate(...args.flatMap(EvmCompiler.uint256ToLimbs)) === 1n;
    }
  );
  return { wasmBytes: simpleCompiler.bytes.length, exported: WebAssembly.Module.exports(module) };
}
```

## 2. Edit the RDF proposals

These are **hypothetical snapshots**, not live ERC-20 balances. They supply the same seven input fields to both the simple function and the richer policy below. Try changing an allowance or block height.

```observable-js
proposals = [
  { id: "eligible", balance: "100", allowance: "80", amount: "70", currentBlock: "1000", unlockBlock: "500", paused: "0", frozen: "0" },
  { id: "overdraft", balance: "40", allowance: "80", amount: "70", currentBlock: "1000", unlockBlock: "500", paused: "0", frozen: "0" },
  { id: "allowanceExhausted", balance: "100", allowance: "30", amount: "70", currentBlock: "1000", unlockBlock: "500", paused: "0", frozen: "0" },
  { id: "timelocked", balance: "100", allowance: "80", amount: "70", currentBlock: "400", unlockBlock: "500", paused: "0", frozen: "0" },
  { id: "paused", balance: "100", allowance: "80", amount: "70", currentBlock: "1000", unlockBlock: "500", paused: "1", frozen: "0" },
  { id: "frozen", balance: "100", allowance: "80", amount: "70", currentBlock: "1000", unlockBlock: "500", paused: "0", frozen: "1" },
  { id: "huge", balance: (1n << 255n).toString(), allowance: (1n << 255n).toString(), amount: (1n << 200n).toString(), currentBlock: "1000", unlockBlock: "500", paused: "0", frozen: "0" },
  { id: "outOfDomain", balance: (1n << 256n).toString(), allowance: "80", amount: "70", currentBlock: "1000", unlockBlock: "500", paused: "0", frozen: "0" }
]
```

This cell generates actual Turtle from the editable proposals:

```observable-js
proposalTurtle = {
  const fields = ["balance", "allowance", "amount", "currentBlock", "unlockBlock", "paused", "frozen"];
  // Use a named dependency, not ...proposals, so the Hub's reactive
  // cell analyser can see changes to the upstream editable RDF proposals.
  const entries = proposals.map(p =>
    "ex:" + p.id + " a ex:Proposal ; " +
    fields.map(k => {
      if (!/^(0|[1-9][0-9]*)$/.test(p[k])) throw Error("Noncanonical integer: " + k);
      return 'ex:' + k + ' "' + p[k] + '"^^xsd:integer';
    }).join(" ; ") + " .");
  return [
    "@prefix ex: <https://example.org/ethereum-demo/> .",
    "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> ."
  ].concat(entries).join("\n");
}
```

### Query the simple predicate

```observable-js
simpleQuery = [
  "PREFIX ex: <https://example.org/ethereum-demo/>",
  "PREFIX evm: <urn:factoidal:ethereum-wasm#>",
  "SELECT ?proposal ?balance ?amount ?enough WHERE {",
  " ?proposal a ex:Proposal ; ex:balance ?balance ; ex:amount ?amount .",
  " BIND(evm:canTransfer256(?balance, ?amount) AS ?enough)",
  "} ORDER BY ?proposal"
].join("\n")
```

```observable-js
simpleRows = {
  const registered = simpleWasm;
  return Factoidal.query(proposalTurtle, simpleQuery);
}
```

Compare this with the seven-input policy below: a proposal may have enough balance, but be **paused, frozen, timelocked or short of allowance**. The value `2^256` is outside Ethereum's uint256 domain and becomes an *unbound* SPARQL result, not a wrapped value.

## 3. A five-condition EVM policy

This 45-byte EVM runtime evaluates the following decision using seven full uint256 inputs:

\[
(\mathrm{balance}\ge\mathrm{amount})\land
(\mathrm{allowance}\ge\mathrm{amount})\land
(\mathrm{block}\ge\mathrm{unlock})\land
(\mathrm{paused}=0)\land(\mathrm{frozen}=0).
\]

```observable-js
policyEvmHex = EvmPolicy.EVM_POLICY_HEX
```

The decoded operations include `PUSH1`, `CALLDATALOAD`, `SWAP1`, `LT`, `ISZERO`, `AND`, `MSTORE` and `RETURN`. The WASM code uses **28 unsigned i64 limbs** (four per EVM word).

```observable-js
policyCompiler = EvmPolicy.compileEvmPolicyToWasm(policyEvmHex)
```

```observable-js
policyDisassembly = pretty(policyCompiler.operations.map(op => ({
  pc: op.pc, opcode: op.opcode, field: op.field ?? op.left ?? "",
  other: op.right ?? "", immediate: op.operand ?? ""
})))
```

```observable-js
policyWasm = {
  const { instance, module } = await WebAssembly.instantiate(policyCompiler.bytes);
  if (WebAssembly.Module.imports(module).length) throw Error("Unexpected WASM imports");
  await Factoidal.registerExtensionFunction(
    "urn:factoidal:ethereum-wasm#eligiblePolicy",
    args => {
      if (args.length !== 7) throw TypeError("Expected seven uint256 words");
      return instance.exports.evaluate(...args.flatMap(EvmCompiler.uint256ToLimbs)) === 1n;
    }
  );
  return { wasmBytes: policyCompiler.bytes.length, signature: policyCompiler.wasmSignature };
}
```

### Edit and execute the SPARQL

```observable-js
policyQuery = [
  "PREFIX ex: <https://example.org/ethereum-demo/>",
  "PREFIX evm: <urn:factoidal:ethereum-wasm#>",
  "SELECT ?proposal ?eligible WHERE {",
  " ?proposal a ex:Proposal ; ex:balance ?balance ;",
  "   ex:allowance ?allowance ; ex:amount ?amount ;",
  "   ex:currentBlock ?block ; ex:unlockBlock ?unlock ;",
  "   ex:paused ?paused ; ex:frozen ?frozen .",
  " BIND(evm:eligiblePolicy(?balance,?allowance,?amount,",
  "   ?block,?unlock,?paused,?frozen) AS ?eligible)",
  "} ORDER BY ?proposal"
].join("\n")
```

```observable-js
policyRows = {
  const registered = policyWasm;
  return Factoidal.query(proposalTurtle, policyQuery);
}
```

```observable-js
policySummary = pretty(policyRows.map(row => ({
  proposal: row.get("proposal").value.split("/").pop(),
  eligible: row.get("eligible")?.value ?? "unbound: outside uint256"
})))
```

Expected: only `eligible` and `huge` pass. Eligibility is a computation over supplied values, **not a real transfer-authorisation verdict**.

## 4. Mutate the Ethereum bytecode and find a SPARQL counterexample

Remove one actual `SWAP1` opcode. Both the WASM program and query answers change. No JavaScript policy is substituted.

```observable-js
mutantEvmHex = policyEvmHex.replace("604435901015", "6044351015")
```

```observable-js
mutantWasm = {
  if (mutantEvmHex === policyEvmHex) throw Error("The EVM mutation did not change the program");
  const compiled = EvmPolicy.compileEvmPolicyToWasm(mutantEvmHex);
  const { instance } = await WebAssembly.instantiate(compiled.bytes);
  await Factoidal.registerExtensionFunction(
    "urn:factoidal:ethereum-wasm#eligibleMutant",
    args => {
      if (args.length !== 7) throw TypeError("Expected seven uint256 words");
      return instance.exports.evaluate(...args.flatMap(EvmCompiler.uint256ToLimbs)) === 1n;
    }
  );
  return { wasmBytes: compiled.bytes.length, changedEvm: mutantEvmHex };
}
```

```observable-js
mutationQuery = [
  "PREFIX ex: <https://example.org/ethereum-demo/>",
  "PREFIX evm: <urn:factoidal:ethereum-wasm#>",
  "SELECT ?proposal ?original ?mutant WHERE {",
  " ?proposal a ex:Proposal ; ex:balance ?balance ;",
  "   ex:allowance ?allowance ; ex:amount ?amount ;",
  "   ex:currentBlock ?block ; ex:unlockBlock ?unlock ;",
  "   ex:paused ?paused ; ex:frozen ?frozen .",
  " BIND(evm:eligiblePolicy(?balance,?allowance,?amount,",
  "   ?block,?unlock,?paused,?frozen) AS ?original)",
  " BIND(evm:eligibleMutant(?balance,?allowance,?amount,",
  "   ?block,?unlock,?paused,?frozen) AS ?mutant)",
  " FILTER(?original != ?mutant)",
  "} ORDER BY ?proposal"
].join("\n")
```

```observable-js
mutationRows = {
  const original = policyWasm;
  const mutated = mutantWasm;
  return Factoidal.query(proposalTurtle, mutationQuery);
}
```

## 5. Join results to the source bytes and generated WASM provenance

The browser computes SHA-256 over the real EVM source and generated WASM. The corresponding RDF carries an explicit **differential-tested-not-proved** status.

```observable-js
policyProvenance = {
  const sha256 = async bytes =>
    Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256", bytes)))
      .map(b => b.toString(16).padStart(2, "0")).join("");
  const source = Uint8Array.from(policyEvmHex.match(/../g).map(b => parseInt(b, 16)));
  return {
    evmSha256: await sha256(source),
    wasmSha256: await sha256(policyCompiler.bytes),
    wasmBytes: policyCompiler.bytes.length,
    assurance: "differential-tested-not-proved"
  };
}
```

```observable-js
provenanceTurtle = proposalTurtle + "\n" + [
  "@prefix evm: <urn:factoidal:ethereum-wasm#> .",
  'evm:eligiblePolicy evm:sourceSha256 "' + policyProvenance.evmSha256 + '" ;',
  ' evm:wasmSha256 "' + policyProvenance.wasmSha256 + '" ;',
  ' evm:assuranceStatus "differential-tested-not-proved" .'
].join("\n")
```

```observable-js
provenanceQuery = [
  "PREFIX ex: <https://example.org/ethereum-demo/>",
  "PREFIX evm: <urn:factoidal:ethereum-wasm#>",
  "SELECT ?proposal ?eligible ?evmHash ?wasmHash ?assurance WHERE {",
  " ?proposal a ex:Proposal ; ex:balance ?balance ;",
  "  ex:allowance ?allowance ; ex:amount ?amount ;",
  "  ex:currentBlock ?block ; ex:unlockBlock ?unlock ;",
  "  ex:paused ?paused ; ex:frozen ?frozen .",
  " BIND(evm:eligiblePolicy(?balance,?allowance,?amount,",
  "  ?block,?unlock,?paused,?frozen) AS ?eligible)",
  " evm:eligiblePolicy evm:sourceSha256 ?evmHash ;",
  "  evm:wasmSha256 ?wasmHash ; evm:assuranceStatus ?assurance .",
  "} ORDER BY ?proposal"
].join("\n")
```

```observable-js
provenanceRows = {
  const registered = policyWasm;
  return Factoidal.query(provenanceTurtle, provenanceQuery);
}
```

## What is proved, tested, and not claimed

The source EVM programs are **hand-authored**, not extracted from deployed contracts. The EVM and WASM numeric domains are correctly constrained to uint256 for the admitted operations, including a four-i64-limb unsigned comparison. Independent EthereumJS Cancun runs have checked the 45-byte policy on 400 vectors; those are finite tests, **not a Lean EVM→WASM refinement theorem**. The SPARQL extension registry, host marshaling and browser WASM runtime remain trusted boundaries. No contract state, gas, storage writes or real transfers are performed by these pure functions.

[Source compiler](https://github.com/danbri/factoidal-core/blob/main/labs/ethereum-wasm-sparql/evm-policy.mjs) · [Differential tests](https://github.com/danbri/factoidal-core/tree/main/labs/ethereum-wasm-sparql) · [Open proof obligation #678](https://github.com/danbri/factoidal-core/issues/678).
