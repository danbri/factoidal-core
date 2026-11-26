# Solidity comparison fixture

`PureCompare.sol` is the source for the `ge(uint256,uint256)` ABI example.
`fixture.json` records the npm compiler distribution and digests, exact
Solidity Standard JSON settings, function selector and complete runtime.
The runtime includes the compiler's CBOR metadata. The test evidence covers
execution of these locally compiled bytes under Shanghai rules.

Run `node scripts/differential/solidity-pure.mjs` from the Lean package after
installing the pinned differential dependencies and building `evm-subset`.
The test needs only the pinned fixture and the existing EthereumJS oracle.

To reproduce the compiler result, install `solc@0.8.30` in a temporary
directory and run this from the fixture directory. Replace the first argument
with the absolute path to that installation's `node_modules/solc` directory.

```sh
node - /tmp/solidity-provenance/node_modules/solc <<'JS'
const assert = require('node:assert/strict')
const { createHash } = require('node:crypto')
const { readFileSync } = require('node:fs')
const { join } = require('node:path')
const compilerDirectory = process.argv[2]
const fixture = JSON.parse(readFileSync('fixture.json', 'utf8'))
const sha256 = data => createHash('sha256').update(data).digest('hex')
assert.equal(sha256(readFileSync(join(compilerDirectory, 'soljson.js'))), fixture.compiler.soljsonSha256)
const solc = require(compilerDirectory)
assert.equal(solc.version(), fixture.compiler.version)
const content = readFileSync(fixture.sourceFile, 'utf8')
assert.equal(sha256(content), fixture.sourceSha256)
const output = JSON.parse(solc.compile(JSON.stringify({
  language: 'Solidity', sources: { [fixture.sourceFile]: { content } }, settings: fixture.settings,
})))
const { evm } = output.contracts[fixture.sourceFile][fixture.contract]
assert.equal(evm.deployedBytecode.object, fixture.runtimeHex)
assert.equal(evm.methodIdentifiers[fixture.methodSignature], fixture.methodIdentifier)
JS
```
