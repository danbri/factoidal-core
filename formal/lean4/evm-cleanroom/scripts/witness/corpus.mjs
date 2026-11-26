/** Published vectors plus independently generated proof fixtures; test data only. */
import assert from 'node:assert/strict'
import { readFileSync } from 'node:fs'
import { gunzipSync } from 'node:zlib'
import { MerklePatriciaTrie, RLP, bytes, hex, nat, fixed, keccak, bytesToBigInt, clone,
  emptyRoot, emptyCode, loadJSON, digest, checkSources, rlpView, proofRequest, checkProof,
  buildStateWitness, checkStateWitness, createMerkleProof } from './oracle.mjs'

const cleanHex = value => hex(bytes(value))
const scalarInput = value => Array.isArray(value) ? value.map(scalarInput) :
  typeof value === 'number' ? nat(value) :
    typeof value === 'string' && value.startsWith('#') ? nat(value.slice(1)) : new TextEncoder().encode(value)
const refused = classification => ({ status: 'refused', classification })
const account = (address, overrides = {}) => ({ address: String(address), exists: true,
  balance: '17', nonce: '1', codeHex: '', storage: [], ...overrides })

// Compact paths are fixture construction, not the implementation under test.
// EthereumJS constructs the valid tries; hand-built nodes below are invalidity controls.
const hp = (path, leaf) => {
  assert(/^[0-9a-f]*$/.test(path))
  return bytes((path.length % 2 ? (leaf ? '3' : '1') : (leaf ? '20' : '00')) + path)
}
const nodeRequest = (node, key = '00'.repeat(32), extra = []) => {
  const encoding = hex(RLP.encode(node))
  return { schemaVersion: 1, root: hex(keccak(bytes(encoding))), key, proof: [encoding, ...extra] }
}
const branch = () => Array.from({ length: 17 }, () => new Uint8Array())

export async function buildCorpus() {
  checkSources()
  const cases = [], oracleCounts = { officialRLP: 0, officialTrieRoots: 0, proofOutcomes: 0, stateOutcomes: 0 }
  const add = (id, family, mode, request, expect, extra = {}) => {
    assert(!cases.some(row => row.id === id), 'unique fixture id: ' + id)
    cases.push({ id, family, mode, request: mode === '--rlp' ? { schemaVersion: 1, ...request } : request, expect, ...extra })
  }
  const addProof = async (id, family, request, expect, oracle = true) => {
    if (oracle && expect.status !== 'refused') {
      try { await checkProof(request, expect) } catch (error) { throw Error(id + ': ' + error, { cause: error }) }
      oracleCounts.proofOutcomes++
    }
    add(id, family, '--mpt-proof', request, expect, { independentOracle: oracle && expect.status !== 'refused' })
  }
  const addState = async (id, family, request, expected, oracle = true) => {
    if (oracle && Array.isArray(expected)) { await checkStateWitness(request, expected); oracleCounts.stateOutcomes++ }
    add(id, family, '--state-witness', request,
      Array.isArray(expected) ? { status: 'authenticated', accounts: expected } : expected,
      { independentOracle: oracle && Array.isArray(expected) })
  }

  for (const [id, test] of Object.entries(loadJSON('mpt-upstream-rlp-valid.json'))) {
    const encoding = cleanHex(test.out)
    assert.equal(hex(RLP.encode(scalarInput(test.in))), encoding, id + ': published input/output pair')
    add('official-rlp/' + id, 'official-rlp', '--rlp', { encoding }, rlpView(encoding), { independentOracle: true })
    oracleCounts.officialRLP++
  }
  for (const [id, test] of Object.entries(loadJSON('mpt-upstream-rlp-invalid.json'))) {
    // EthereumJS accepts empty input as an API sentinel. Requiring an exact
    // canonical round trip distinguishes that sentinel from an encoded item.
    assert.throws(() => rlpView(test.out), undefined, id + ': invalid encoding or noncanonical sentinel')
    add('official-rlp/' + id, 'official-rlp', '--rlp', { encoding: cleanHex(test.out) }, refused('invalid'),
      { independentOracle: true })
    oracleCounts.officialRLP++
  }
  assert.equal(oracleCounts.officialRLP, 54)
  for (const [id, encoding, width, valid] of [
    ['empty-zero-width', '80', 0, true], ['empty-zero', '80', 32, true], ['raw-zero', '00', 32, false],
    ['one', '01', 1, true], ['leading-zero', '820001', 32, false], ['list-as-scalar', 'c0', 32, false],
    ['nonce-max', '88' + 'ff'.repeat(8), 8, true], ['nonce-overflow', '89' + '01'.repeat(9), 8, false],
    ['word-max', 'a0' + 'ff'.repeat(32), 32, true], ['word-overflow', 'a1' + '01'.repeat(33), 32, false],
    ['nonzero-zero-width', '01', 0, false],
  ]) add('rlp-scalar/' + id, 'rlp-controls', '--rlp', { encoding, integerBytes: width },
    valid ? rlpView(encoding, width) : refused('invalid'))
  for (const [id, encoding] of [
    ['trailing-item', '8080'], ['trailing-empty-list', 'c0c0'], ['nested-noncanonical-byte', 'c28100'],
    ['nested-noncanonical-list', 'c2f800'], ['nested-truncated-long', 'c2b838'],
    ['claimed-uint64-length', 'bfffffffffffffffff'], ['long-list-claimed-uint64-length', 'ffffffffffffffffff'],
  ]) add('rlp-controls/' + id, 'rlp-controls', '--rlp', { encoding }, refused('invalid'))
  for (const length of [55, 56, 255, 256]) {
    const encoding = hex(RLP.encode(new Uint8Array(length).fill(0xab)))
    add('rlp-controls/length-' + length, 'rlp-controls', '--rlp', { encoding }, rlpView(encoding))
  }

  // The published roots qualify the independent trie constructor before its proofs are used.
  for (const [id, test] of Object.entries(loadJSON('mpt-upstream-secure-trie.json'))) {
    const trie = new MerklePatriciaTrie({ useKeyHashing: true })
    for (const [key, value] of Object.entries(test.in)) await trie.put(bytes(key), bytes(value))
    assert.equal(hex(trie.root()), cleanHex(test.root), id + ': exact published secure-trie root')
    oracleCounts.officialTrieRoots++
    for (const [key, value] of Object.entries(test.in)) {
      const request = { schemaVersion: 1, root: hex(trie.root()), key: hex(keccak(bytes(key))),
        proof: (await createMerkleProof(trie, bytes(key))).map(hex) }
      await addProof('official-trie/' + id + '/' + key, 'official-trie', request,
        { status: 'present', valueHex: cleanHex(value) })
    }
    const missing = fixed(0xffffffffffffffffffffffffffffffffffffffffn, 20)
    assert(!Object.hasOwn(test.in, '0x' + hex(missing)))
    await addProof('official-trie/' + id + '/absent', 'official-trie',
      { schemaVersion: 1, root: hex(trie.root()), key: hex(keccak(missing)),
        proof: (await createMerkleProof(trie, missing)).map(hex) }, { status: 'absent' })
  }
  assert.equal(oracleCounts.officialTrieRoots, 3)

  const historicalRaw = gunzipSync(Buffer.from(readFileSync(new URL(
    '../../evidence/frontier-mainnet-46146-account-proofs.json.gz.b64', import.meta.url), 'utf8'), 'base64'))
  assert.equal(digest(historicalRaw), '9c9286d7c9500aca5426b7bf44bc74b19f84d2b16761dfb10ea7948bbef17924')
  const historical = JSON.parse(historicalRaw), historicalAccounts = [], historicalExpected = []
  assert.equal(cleanHex(historical.parentHeader.stateRoot), '691fc4f4d21d10787902e8f3266711f1d640e75fedbeb406dc0b8d3096128436')
  for (const [index, row] of historical.accounts.entries()) {
    const proof = row.accountProof.map(cleanHex), exists = index !== 1
    const value = hex(RLP.encode([nat(row.nonce), nat(row.balance), bytes(emptyRoot), bytes(emptyCode)]))
    await addProof('historical-frontier/' + index, 'historical',
      { schemaVersion: 1, root: cleanHex(historical.parentHeader.stateRoot), key: hex(keccak(bytes(row.address))), proof },
      exists ? { status: 'present', valueHex: value } : { status: 'absent' })
    historicalAccounts.push({ address: BigInt(row.address).toString(), codeHex: '', accountProof: proof, storage: [] })
    historicalExpected.push(account(BigInt(row.address).toString(),
      { exists, balance: BigInt(row.balance).toString(), nonce: BigInt(row.nonce).toString() }))
  }
  await addState('historical-frontier/admission', 'historical',
    { schemaVersion: 1, stateRoot: cleanHex(historical.parentHeader.stateRoot), accounts: historicalAccounts }, historicalExpected)

  const small = new MerklePatriciaTrie({ useKeyHashing: false })
  const keyA = bytes('00'.repeat(32)), keyB = bytes('00'.repeat(31) + '01')
  await small.put(keyA, bytes('01')); await small.put(keyB, bytes('02'))
  const base = await proofRequest(small, keyA), present = { status: 'present', valueHex: '01' }
  await addProof('mpt/inline-empty-suffix-leaf', 'mpt-structure', base, present)
  await addProof('mpt/inline-proof-root-only', 'mpt-structure', { ...base, proof: [base.proof[0]] }, present)
  await addProof('mpt/inline-second-leaf', 'mpt-structure', await proofRequest(small, keyB), { status: 'present', valueHex: '02' })
  await addProof('mpt/empty-branch-child', 'mpt-structure', await proofRequest(small, bytes('00'.repeat(31) + '02')), { status: 'absent' })
  await addProof('mpt/extension-mismatch', 'mpt-structure', await proofRequest(small, bytes('10' + '00'.repeat(31))), { status: 'absent' })
  await addProof('mpt/unordered', 'mpt-proofbag', { ...base, proof: [...base.proof].reverse() }, present)
  await addProof('mpt/duplicate-nodes', 'mpt-proofbag', { ...base, proof: [...base.proof, ...base.proof] }, present)
  await addProof('mpt/unused-valid-node', 'mpt-proofbag', { ...base, proof: [...base.proof, 'c0'] }, present)
  await addProof('mpt/unused-malformed-node', 'mpt-proofbag', { ...base, proof: [...base.proof, 'ff'] }, present, false)
  await addProof('mpt/wrong-root', 'mpt-negative', { ...base, root: 'ff'.repeat(32) }, refused('invalid'), false)
  await addProof('mpt/missing-root', 'mpt-negative', { ...base, proof: base.proof.slice(1) }, refused('invalid'), false)
  const hashed = new MerklePatriciaTrie({ useKeyHashing: false })
  await hashed.put(keyA, bytes('11'.repeat(29))); await hashed.put(keyB, bytes('22'.repeat(29)))
  const completeHashed = await proofRequest(hashed, keyA)
  assert(completeHashed.proof.length >= 2)
  const missingReferenced = { ...completeHashed, proof: [completeHashed.proof[0]] }
  await assert.rejects(() => checkProof(missingReferenced, { status: 'present', valueHex: '11'.repeat(29) }))
  await addProof('mpt/missing-hashed-child', 'mpt-negative', missingReferenced, refused('invalid'), false)
  const changedNode = clone(base); changedNode.proof[0] += '80'
  await addProof('mpt/mutated-root-bytes', 'mpt-negative', changedNode, refused('invalid'), false)
  await addProof('mpt/empty-trie', 'mpt-structure', { schemaVersion: 1, root: emptyRoot, key: hex(keyA), proof: [] }, { status: 'absent' })
  await addProof('mpt/empty-trie-redundant', 'mpt-proofbag',
    { schemaVersion: 1, root: emptyRoot, key: hex(keyA), proof: ['80', 'ff'] }, { status: 'absent' }, false)
  const only = new MerklePatriciaTrie({ useKeyHashing: false }); await only.put(keyA, bytes('01'))
  await addProof('mpt/leaf-mismatch', 'mpt-structure', await proofRequest(only, keyB), { status: 'absent' })

  for (const length of [28, 29]) {
    const trie = new MerklePatriciaTrie({ useKeyHashing: false }), value = new Uint8Array(length).fill(0x33)
    await trie.put(keyA, value); await trie.put(keyB, value)
    // Empty-suffix leaf = list prefix + path(0x20) + byte-string prefix + value.
    assert.equal(RLP.encode([bytes('20'), value]).length, length + 3)
    await addProof('mpt/child-encoding-' + (length + 3), 'mpt-structure', await proofRequest(trie, keyA),
      { status: 'present', valueHex: hex(value) })
  }
  const oneNibble = new MerklePatriciaTrie({ useKeyHashing: false })
  for (const prefix of ['10', '11']) await oneNibble.put(bytes(prefix + '00'.repeat(31)), bytes('05'))
  await addProof('mpt/one-nibble-extension', 'mpt-structure',
    await proofRequest(oneNibble, bytes('10' + '00'.repeat(31))), { status: 'present', valueHex: '05' })
  const longest = new MerklePatriciaTrie({ useKeyHashing: false })
  await longest.put(keyA, bytes('07'))
  for (let depth = 0; depth < 64; depth++) await longest.put(bytes('0'.repeat(depth) + '1' + '0'.repeat(63 - depth)), bytes('08'))
  await addProof('mpt/sixty-five-path-nodes', 'mpt-resource', await proofRequest(longest, keyA), { status: 'present', valueHex: '07' })
  await addProof('mpt/proof-nodes-at-cap', 'mpt-resource',
    { ...base, proof: [...base.proof, ...Array(128 - base.proof.length).fill('')] }, present, false)
  await addProof('mpt/proof-nodes-one-over', 'mpt-resource',
    { ...base, proof: [...base.proof, ...Array(129 - base.proof.length).fill('')] }, refused('resource'), false)
  for (const length of [4096, 4097]) await addProof('mpt/unused-node-bytes-' + length, 'mpt-resource',
    { ...base, proof: [...base.proof, '00'.repeat(length)] }, length === 4096 ? present : refused('resource'), false)

  for (const [id, raw] of [
    ['hp-invalid-flag', [bytes('40' + '00'.repeat(32)), bytes('01')]],
    ['hp-even-padding', [bytes('21' + '00'.repeat(32)), bytes('01')]],
    ['hp-empty', [bytes(''), bytes('01')]],
    ['leaf-short-path', [hp('0'.repeat(63), true), bytes('01')]],
    ['leaf-long-path', [hp('0'.repeat(65), true), bytes('01')]],
    ['empty-extension', [hp('', false), bytes('11'.repeat(32))]],
    ['extension-long-path', [hp('0'.repeat(65), false), bytes('11'.repeat(32))]],
    ['path-is-list', [[], bytes('01')]],
    ['leaf-value-is-list', [hp('0'.repeat(64), true), []]],
    ['arity-one', [bytes('01')]], ['arity-three', [bytes('01'), bytes('02'), bytes('03')]],
    ['arity-sixteen', branch().slice(1)], ['arity-eighteen', [...branch(), bytes('')]],
  ]) await addProof('mpt-invalid/' + id, 'mpt-negative', nodeRequest(raw), refused('invalid'), false)
  for (const width of [1, 31, 33]) {
    const raw = branch(); raw[0] = new Uint8Array(width).fill(0x77)
    await addProof('mpt-invalid/reference-width-' + width, 'mpt-negative', nodeRequest(raw), refused('invalid'), false)
  }
  {
    const raw = branch(); raw[0] = [hp('0'.repeat(63), true), new Uint8Array(30).fill(1)]
    assert(RLP.encode(raw[0]).length >= 32)
    await addProof('mpt-invalid/oversized-inline-child', 'mpt-negative', nodeRequest(raw), refused('invalid'), false)
  }
  {
    const child = [bytes('20'), bytes('01')], raw = [hp('0'.repeat(64), false), keccak(RLP.encode(child))]
    assert(RLP.encode(child).length < 32)
    await addProof('mpt-invalid/hash-reference-to-short-node', 'mpt-negative',
      nodeRequest(raw, hex(keyA), [hex(RLP.encode(child))]), refused('invalid'), false)
  }
  {
    const request = nodeRequest([hp('0'.repeat(64), true), bytes('01')])
    request.proof[0] += '80'; request.root = hex(keccak(bytes(request.proof[0])))
    await addProof('mpt-invalid/root-trailing-rlp', 'mpt-negative', request, refused('invalid'), false)
  }
  {
    // The selected pointer is empty; the other child is malformed RLP. Validating
    // only the selected branch would incorrectly certify this used node.
    const encoded = 'd2' + '80'.repeat(15) + '8100' + '80'
    await addProof('mpt-invalid/noncanonical-unselected-child', 'mpt-negative',
      { schemaVersion: 1, root: hex(keccak(bytes(encoded))), key: hex(keyA), proof: [encoded] }, refused('invalid'), false)
  }

  const records = [
    account('1', { nonce: '7', balance: '1000000000000', codeHex: '600160005500',
      storage: [{ key: '0', value: '9' }, { key: '1', value: '0' }, { key: '2', value: '15' },
        { key: ((1n << 256n) - 1n).toString(), value: ((1n << 256n) - 1n).toString() }] }),
    account('2', { nonce: '3', balance: '41', codeHex: '00', storage: [{ key: '0', value: '3' }] }),
    account('3', { exists: false, nonce: '0', balance: '0' }),
  ]
  const state = await buildStateWitness(records)
  await addState('state/multiple-accounts-storage', 'state-binding', state, records)
  const shuffledState = clone(state)
  for (const row of shuffledState.accounts) {
    row.accountProof.reverse()
    for (const slot of row.storage) slot.proof.reverse()
  }
  await addState('state/unordered-proofs', 'state-binding', shuffledState, records)
  const emptyAccount = [account('9', { balance: '0', nonce: '0' })]
  await addState('state/present-empty-account', 'state-binding', await buildStateWitness(emptyAccount), emptyAccount)
  const absent = [account('9', { exists: false, balance: '0', nonce: '0' })]
  await addState('state/empty-state-absence', 'state-binding', await buildStateWitness(absent), absent)
  const maxima = [account(((1n << 160n) - 1n).toString(),
    { nonce: ((1n << 64n) - 1n).toString(), balance: ((1n << 256n) - 1n).toString() })]
  await addState('state/scalar-width-maxima', 'state-binding', await buildStateWitness(maxima), maxima)

  const mutateState = async (id, mutate, classification = 'invalidWitness', extra = {}) => {
    const request = clone(state); mutate(request)
    await addState('state-invalid/' + id, 'state-negative', request, { ...refused(classification), ...extra }, false)
  }
  await mutateState('code-hash-mismatch', request => { request.accounts[0].codeHex += '00' },
    'invalidWitness', { reason: 'code-hash-mismatch' })
  await mutateState('state-root-mismatch', request => { request.stateRoot = 'ff'.repeat(32) })
  await mutateState('missing-account-root', request => { request.accounts[0].accountProof = [] })
  await mutateState('storage-account-swap', request => { request.accounts[0].storage[0].proof = request.accounts[1].storage[0].proof })
  await mutateState('storage-missing-node', request => { request.accounts[0].storage[0].proof = [] })
  await mutateState('duplicate-account', request => { request.accounts.push(clone(request.accounts[0])) },
    'invalidWitness', { reason: 'duplicate-account' })
  await mutateState('duplicate-storage-key', request => { request.accounts[0].storage.push(clone(request.accounts[0].storage[0])) },
    'invalidWitness', { reason: 'duplicate-storage-key' })
  await mutateState('absent-account-with-code', request => { request.accounts[2].codeHex = '00' },
    'invalidWitness', { reason: 'absent-account-has-code' })
  await mutateState('absent-account-requested-storage', request => { request.accounts[2].storage.push({ key: '0', proof: [] }) },
    'unsupported', { reason: 'absent-account-storage-request' })
  await mutateState('proof-nodes-one-over', request => { request.accounts[0].accountProof = Array(129).fill('') }, 'resourceLimit')
  await mutateState('unused-node-one-over', request => { request.accounts[0].accountProof.push('00'.repeat(4097)) }, 'resourceLimit')

  // Commit malformed account tuples under genuine trie roots: hashing the bytes
  // is insufficient; admission must independently check account scalar semantics.
  const fields = [nat(1), nat(2), bytes(emptyRoot), bytes(emptyCode)]
  for (const [id, malformed] of [
    ['nonce-leading-zero', [bytes('0001'), ...fields.slice(1)]],
    ['nonce-zero-byte', [bytes('00'), ...fields.slice(1)]],
    ['nonce-overflow', [bytes('01'.repeat(9)), ...fields.slice(1)]],
    ['balance-leading-zero', [fields[0], bytes('0002'), ...fields.slice(2)]],
    ['balance-overflow', [fields[0], bytes('01'.repeat(33)), ...fields.slice(2)]],
    ['account-arity-three', fields.slice(1)], ['account-arity-five', [...fields, bytes('')]],
    ['nonce-list', [[], ...fields.slice(1)]],
    ['storage-root-width', [fields[0], fields[1], bytes('01'.repeat(31)), fields[3]]],
    ['code-hash-width', [...fields.slice(0, 3), bytes('01'.repeat(31))]],
    ['account-is-scalar', bytes('01')],
  ]) {
    const trie = new MerklePatriciaTrie({ useKeyHashing: true })
    await trie.put(fixed(1, 20), RLP.encode(malformed))
    await addState('state-invalid/' + id, 'state-negative', { schemaVersion: 1, stateRoot: hex(trie.root()),
      accounts: [{ address: '1', codeHex: '', accountProof: (await createMerkleProof(trie, fixed(1, 20))).map(hex), storage: [] }] },
    refused('invalidWitness'), false)
  }
  for (const [id, encoded] of [
    ['storage-zero', '80'], ['storage-zero-byte', '00'], ['storage-leading-zero', '820001'],
    ['storage-overflow', 'a1' + '01'.repeat(33)], ['storage-list', 'c0'], ['storage-trailing-item', '0180'],
  ]) {
    const trie = new MerklePatriciaTrie({ useKeyHashing: true }), storage = new MerklePatriciaTrie({ useKeyHashing: true })
    await storage.put(fixed(0, 32), bytes(encoded))
    await trie.put(fixed(1, 20), RLP.encode([nat(1), nat(2), storage.root(), bytes(emptyCode)]))
    await addState('state-invalid/' + id, 'state-negative', { schemaVersion: 1, stateRoot: hex(trie.root()),
      accounts: [{ address: '1', codeHex: '', accountProof: (await createMerkleProof(trie, fixed(1, 20))).map(hex),
        storage: [{ key: '0', proof: (await createMerkleProof(storage, fixed(0, 32))).map(hex) }] }] },
    refused('invalidWitness'), false)
  }

  const inputError = { status: 'inputError' }
  const transport = (id, mode, request, extra = {}) =>
    add('transport/' + id, 'transport', mode, request, inputError, { exitCode: 2, ...extra })
  add('transport/rlp-without-crypto-opt-in', 'transport', '--rlp', { encoding: '80' }, rlpView('80'), { optIn: false })
  transport('proof-without-crypto-opt-in', '--mpt-proof', base,
    { optIn: false, reasonIncludes: 'experimental Keccak opt-in required' })
  transport('state-without-crypto-opt-in', '--state-witness', state, { optIn: false })
  for (const field of ['balance', 'nonce', 'exists', 'storageRoot', 'codeHash']) {
    const request = clone(state); request.accounts[0][field] = field === 'exists' ? true : '0'
    transport('untrusted-account-' + field, '--state-witness', request, { reasonIncludes: 'unexpected field' })
  }
  {
    const request = clone(state); request.accounts[0].storage[0].value = '999'
    transport('untrusted-storage-value', '--state-witness', request, { reasonIncludes: 'unexpected field' })
  }
  for (const encoding of ['f', 'gg']) transport('malformed-hex-' + encoding, '--rlp', { encoding })
  const raw = JSON.stringify(state)
  for (const [id, rawRequest] of [
    ['duplicate-root', raw.replace('"stateRoot":', '"stateRoot":"' + state.stateRoot + '","stateRoot":')],
    ['escaped-duplicate-root', raw.replace('"stateRoot":', '"stateR\\u006fot":"' + state.stateRoot + '","stateRoot":')],
    ['duplicate-account-address', raw.replace('"address":"1"', '"address":"1","address":"1"')],
    ['duplicate-storage-proof', raw.replace('"proof":', '"proof":[],"proof":')],
  ]) transport(id, '--state-witness', state, { rawRequest, reasonIncludes: 'duplicate JSON field' })
  transport('nested-json-limit', '--state-witness', state,
    { rawRequest: '['.repeat(65) + '0' + ']'.repeat(65), reasonIncludes: 'json-nesting-limit' })
  transport('numeric-exponent-limit', '--state-witness', state,
    { rawRequest: '{"schemaVersion":1e1000000}', reasonIncludes: 'json-exponent-limit' })

  return { cases, oracleCounts, baseState: state, baseRecords: records }
}
