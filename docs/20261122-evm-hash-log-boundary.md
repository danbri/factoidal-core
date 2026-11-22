# EVM hash and log opcode boundary

`KECCAK256` streams immutable memory views through a 25-lane Keccak-f[1600]
state. It absorbs 136-byte rate blocks with Ethereum's `0x01` delimiter
and final `0x80` bit. The two bits share `0x81` at the last rate byte.
The dispatcher checks the EVM gas charge before reading memory and refuses
funded requests over 16 MiB as an implementation resource limit. Theorems
connect the actual dispatcher to its memory window and sponge, prove the
padding and byte-range properties, and bound the number of absorbed blocks.
The backing function can traverse previous memory updates.
[Keccak source](../formal/lean4/evm-cleanroom/EVMCleanroom/Keccak.lean) ·
[Hash and log scope, #796](https://github.com/danbri/factoidal-core/issues/796)

`LOG0` through `LOG4` consume offset, length and the requested topics in
stack pop order. Each log records the current frame address and a read-only
view of paid memory. Emission stores one journal entry, independent of the
payload length. The frame pays for the data and topics before the static
check. A standalone frame retains its entry journal on REVERT and on
exceptional halt.
[Dispatch and journal proofs](../formal/lean4/evm-cleanroom/EVMCleanroom/HashLogProofs.lean)

## Experimental crypto risk

The clean-room EVM's experimental native Keccak path is disabled by default.
`Keccak.Acceptance` carries explicit consent, and the runtime flag is
`--dangerously-enable-unverified-keccak`. The reviewed scope covers
experimental public Ethereum replay and public or generated tests. The
reference vectors check hash values. Private-input handling, independent
formal equivalence to a cryptographic reference and constant-time host
execution remain open.
[Crypto policy](../skills/crypto-policy/SKILL.md) ·
[Risk rules](../skills/lean-risk-flags/SKILL.md) ·
[XKCP-pinned known answers](../formal/lean4/evm-cleanroom/evidence/frontier-keccak-vectors.json)

## Executable checks

The native comparison runs 80 programs against pinned EthereumJS with
Cancun rules. It uses the 24 XKCP-pinned inputs to compare hash bytes
against noble and the Lean opcode output. The other cases include exact
gas boundaries, immutable log data, static and operand errors, and nested
log commit and rollback. The native-only controls cover opt-in propagation
and default refusal, gas precedence over the hash cap, and refusal to
serialize an oversized log observation. The gate also rejects four
deliberate mutations of compared outputs.
[Native comparison](../formal/lean4/evm-cleanroom/scripts/differential/hash-log.mjs)
