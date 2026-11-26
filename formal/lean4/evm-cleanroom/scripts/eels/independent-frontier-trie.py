#!/usr/bin/env python3
"""Independent dependency-free Frontier account Merkle Patricia proof/replay.

Implements Keccak-f[1600], Ethereum RLP, secure hexary Patricia proof lookup,
and sparse account updates. It never uses EthereumJS as an oracle. Only
non-deleting account updates are supported here. For Ethereum mainnet 2015,
verify all three historical account proofs before accepting any result.
"""
import json
import sys

MASK = (1 << 64) - 1
RC = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a,
    0x8000000080008000, 0x000000000000808b, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008a,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800a, 0x800000008000000a, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
]
ROT = [
    [0, 36, 3, 41, 18], [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61], [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
]

def rot(a, n):
    return ((a << n) | (a >> (64 - n))) & MASK if n else a

def keccak_f(s):
    for rc in RC:
        c = [s[x] ^ s[x+5] ^ s[x+10] ^ s[x+15] ^ s[x+20]
             for x in range(5)]
        d = [c[(x-1)%5] ^ rot(c[(x+1)%5], 1) for x in range(5)]
        for y in range(5):
            for x in range(5):
                s[x+5*y] ^= d[x]
        b = [0]*25
        for y in range(5):
            for x in range(5):
                b[y%5 + 5*((2*x + 3*y)%5)] = rot(s[x+5*y], ROT[x][y])
        for y in range(5):
            for x in range(5):
                s[x+5*y] = b[x+5*y] ^ (
                    (~b[(x+1)%5+5*y]) & b[(x+2)%5+5*y])
        s[0] ^= rc

def keccak256(blob):
    rate = 136
    pad = bytearray(blob)
    pad.append(0x01)             # Ethereum Keccak domain, not SHA3-256
    while len(pad) % rate:
        pad.append(0)
    # When the suffix occupies the final rate byte, both bits form 0x81.
    pad[-1] |= 0x80
    state = [0]*25
    for start in range(0, len(pad), rate):
        block = pad[start:start+rate]
        for i in range(rate//8):
            state[i] ^= int.from_bytes(block[8*i:8*i+8], 'little')
        keccak_f(state)
    return b''.join(state[i].to_bytes(8, 'little') for i in range(4))

def length_prefix(n, offset):
    if n < 56:
        return bytes([offset+n])
    v = n.to_bytes((n.bit_length()+7)//8, 'big')
    return bytes([offset+55+len(v)])+v

def rlp_enc(obj):
    if isinstance(obj, int):
        if obj < 0:
            raise ValueError('negative RLP integer')
        return rlp_enc(obj.to_bytes((obj.bit_length()+7)//8, 'big'))
    if isinstance(obj, (list, tuple)):
        data = b''.join(rlp_enc(x) for x in obj)
        return length_prefix(len(data), 0xc0)+data
    assert isinstance(obj, bytes)
    if len(obj) == 1 and obj[0] < 0x80:
        return obj
    return length_prefix(len(obj), 0x80)+obj

def decode_part(blob, i):
    if i >= len(blob):
        raise ValueError('RLP truncated')
    first = blob[i]
    if first <= 0x7f:
        return bytes([first]), i+1
    if first <= 0xb7:
        n = first-0x80
        if i+1+n > len(blob):
            raise ValueError('short RLP string')
        return blob[i+1:i+1+n], i+1+n
    if first <= 0xbf:
        width = first-0xb7
        if i+1+width > len(blob):
            raise ValueError('short RLP length')
        n = int.from_bytes(blob[i+1:i+1+width], 'big')
        if n < 56 or (width>1 and blob[i+1]==0):
            raise ValueError('noncanonical RLP length')
        if i+1+width+n > len(blob):
            raise ValueError('truncated long RLP')
        return blob[i+1+width:i+1+width+n], i+1+width+n
    if first <= 0xf7:
        return decode_list(blob, i+1, i+1+first-0xc0)
    width = first-0xf7
    if i+1+width > len(blob):
        raise ValueError('short RLP list length')
    n = int.from_bytes(blob[i+1:i+1+width], 'big')
    if n < 56 or (width>1 and blob[i+1]==0):
        raise ValueError('noncanonical RLP list length')
    return decode_list(blob, i+1+width, i+1+width+n)

def decode_list(blob, pos, end):
    if end > len(blob):
        raise ValueError('truncated RLP list')
    values = []
    while pos < end:
        item, pos = decode_part(blob, pos)
        if pos > end:
            raise ValueError('RLP child crosses parent boundary')
        values.append(item)
    return values, pos

def rlp_dec(blob):
    value, i = decode_part(blob, 0)
    if i != len(blob) or rlp_enc(value) != blob:
        raise ValueError('noncanonical or trailing RLP')
    return value

def nibbles(data):
    return [z for byte in data for z in (byte >> 4, byte & 15)]

def hp_dec(data):
    ns = nibbles(data)
    if not ns or ns[0] > 3:
        raise ValueError('invalid hex-prefix')
    flag = ns[0]
    odd = flag & 1
    if not odd and ns[1] != 0:
        raise ValueError('nonzero HP padding')
    return ns[1 if odd else 2:], bool(flag & 2)

def hp_enc(ns, leaf):
    if any(x < 0 or x > 15 for x in ns):
        raise ValueError('invalid nibble')
    odd = len(ns) % 2
    vec = [2*(bool(leaf))+odd] + (ns if odd else [0]+ns)
    return bytes(vec[i]*16+vec[i+1] for i in range(0, len(vec), 2))

def child_ref(rlp):
    return rlp_dec(rlp) if len(rlp) < 32 else keccak256(rlp)

class SparseTrie:
    def __init__(self, root):
        self.root = root
        self.db = {}
    def load_proof(self, nodes):
        if not nodes or keccak256(nodes[0]) != self.root:
            raise ValueError('wrong authenticated proof root')
        for node in nodes:
            if not isinstance(rlp_dec(node), list):
                raise ValueError('proof contains a non-node')
            self.db[keccak256(node)] = node
    def read_node(self, ref):
        if isinstance(ref, list):
            return ref
        if not ref:
            return None
        if len(ref) == 32:
            if ref not in self.db:
                raise ValueError('missing authenticated path node')
            return rlp_dec(self.db[ref])
        if len(ref) < 32:
            node = rlp_dec(ref)
            if isinstance(node, list):
                return node
        raise ValueError('invalid MPT node reference')
    def lookup(self, address):
        remaining = nibbles(keccak256(address))
        node = self.read_node(self.root)
        while node is not None:
            if len(node) == 17:
                if not remaining:
                    return node[16] or None
                node = self.read_node(node[remaining[0]])
                remaining = remaining[1:]
            elif len(node) == 2:
                prefix, leaf = hp_dec(node[0])
                if remaining[:len(prefix)] != prefix:
                    return None
                remaining = remaining[len(prefix):]
                if leaf:
                    return node[1] if not remaining else None
                node = self.read_node(node[1])
            else:
                raise ValueError('invalid MPT node arity')
        return None
    def save(self, node):
        serialized = rlp_enc(node)
        self.db[keccak256(serialized)] = serialized
        return child_ref(serialized)
    def leaf(self, path, value):
        return self.save([hp_enc(path, True), value])
    def extension(self, path, nxt):
        return self.save([hp_enc(path, False), nxt]) if path else nxt
    def change(self, ref, key, value):
        node = self.read_node(ref)
        if node is None:
            return self.leaf(key, value)
        if len(node) == 17:
            next_node = list(node)
            if not key:
                next_node[16] = value
            else:
                next_node[key[0]] = self.change(node[key[0]], key[1:], value)
            return self.save(next_node)
        if len(node) != 2:
            raise ValueError('invalid MPT node')
        old, leaf = hp_dec(node[0])
        count = 0
        while count < min(len(old), len(key)) and old[count] == key[count]:
            count += 1
        if count == len(old):
            if leaf:
                if count == len(key):
                    return self.leaf(old, value)
                branch = [b'']*17
                branch[16] = node[1]
                branch[key[count]] = self.leaf(key[count+1:], value)
                return self.extension(old, self.save(branch))
            return self.extension(old,
                self.change(node[1], key[count:], value))
        branch = [b'']*17
        old_suffix = old[count:]
        new_suffix = key[count:]
        if not old_suffix:
            branch[16] = node[1] if leaf else b''
        elif leaf:
            branch[old_suffix[0]] = self.leaf(old_suffix[1:], node[1])
        else:
            branch[old_suffix[0]] = self.extension(old_suffix[1:], node[1])
        if not new_suffix:
            branch[16] = value
        else:
            branch[new_suffix[0]] = self.leaf(new_suffix[1:], value)
        return self.extension(old[:count], self.save(branch))
    def put(self, address, value):
        node_ref = self.change(self.root, nibbles(keccak256(address)), value)
        if isinstance(node_ref, list):
            self.root = keccak256(rlp_enc(node_ref))
        elif len(node_ref) == 32:
            self.root = node_ref
        else:
            self.root = keccak256(node_ref)

EMPTY_CODE = keccak256(b'')
EMPTY_STORAGE = keccak256(rlp_enc(b''))

def account_decode(value):
    if value is None:
        return (0, 0, EMPTY_STORAGE, EMPTY_CODE, False)
    parts = rlp_dec(value)
    if not isinstance(parts, list) or len(parts) != 4:
        raise ValueError('account must have four RLP fields')
    nonce, balance, storage, code = parts
    if len(storage) != 32 or len(code) != 32:
        raise ValueError('incorrect account hash lengths')
    return (int.from_bytes(nonce, 'big'),
        int.from_bytes(balance, 'big'), storage, code, True)

def account_encode(nonce, balance, storage, code):
    if nonce < 0 or nonce >= 2**64 or balance < 0 or balance >= 2**256:
        raise ValueError('invalid account integer')
    return rlp_enc([nonce, balance, storage, code])

def verify_historical(witness):
    root = bytes.fromhex(witness['parentHeader']['stateRoot'][2:])
    # Independent fixed Ethereum vectors. These detect using SHA3 instead
    # of Ethereum's original Keccak padding.
    assert keccak256(b'').hex() == \
        'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470'
    assert keccak256(rlp_enc([])).hex() == \
        '1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347'
    assert keccak256(rlp_enc(b'')).hex() == \
        '56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421'
    expected_intermediate = bytes.fromhex(
        '96a8e009d2b88b1483e6941e6812e32263b05683fac202abc622a3e31aed1957')
    expected_final = bytes.fromhex(
        '0e0df2706b0a4fb8bd08c9246d472abbe850af446405d9eba1db41db18b4a169')
    t = SparseTrie(root)
    accounts = witness['accounts']
    if len(accounts) != 3:
        raise ValueError('expected three participants')
    for p in accounts:
        t.load_proof([bytes.fromhex(s[2:]) for s in p['accountProof']])
    actual = []
    for p in accounts:
        addr = bytes.fromhex(p['address'][2:])
        decoded = account_decode(t.lookup(addr))
        if decoded[0] != int(p['nonce'], 16) or \
                decoded[1] != int(p['balance'], 16):
            raise ValueError('account nonce/balance contradicted Merkle proof')
        if decoded[4]:
            if decoded[2].hex() != p['storageHash'][2:] or \
                    decoded[3].hex() != p['codeHash'][2:]:
                raise ValueError('account code/storage hash contradicted proof')
        elif p['codeHash'] != '0x'+'00'*32 or \
                p['storageHash'] != '0x'+'00'*32:
            raise ValueError('absent account RPC hashes not zero')
        actual.append((addr, decoded))
    sender, receiver, miner = [item[1] for item in actual]
    if sender[0] != 0 or sender[3] != EMPTY_CODE or \
            receiver[3] != EMPTY_CODE:
        raise ValueError('not the no-code Frontier first transaction')
    gas_used, gas_price, amount = 21000, 50000000000000, 31337
    fee = gas_used * gas_price
    if sender[1] < gas_used*gas_price+amount:
        raise ValueError('not enough authenticated sender balance')
    changes = [
        (sender[0]+1, sender[1]-fee-amount, sender[2], sender[3]),
        (receiver[0], receiver[1]+amount, receiver[2], receiver[3]),
        (miner[0], miner[1]+fee, miner[2], miner[3]),
    ]
    for (addr, _), account in zip(actual, changes):
        t.put(addr, account_encode(*account))
    if t.root != expected_intermediate:
        raise ValueError('REAL INTERMEDIATE STATE ROOT MISMATCH: '+t.root.hex())
    intermediate = t.root
    miner_address = actual[2][0]
    nonce, balance, storage, code = changes[2]
    t.put(miner_address,
        account_encode(nonce, balance+5*10**18, storage, code))
    if t.root != expected_final:
        raise ValueError('REAL POST-BLOCK STATE ROOT MISMATCH: '+t.root.hex())
    return {
        'status':'pass',
        'kind':'independent-pure-python-keccak-rlp-secure-mpt-frontier-mainnet',
        'prestateRoot':root.hex(),
        'intermediateRoot':intermediate.hex(),
        'postBlockRoot':t.root.hex(),
        'accountsVerified':len(accounts),
        'recipientNonexistentBeforeTransaction':not receiver[4],
        'senderWeiBefore':str(sender[1]),
        'minerWeiBefore':str(miner[1]),
        'gasUsed':gas_used,
        'transactionFeeWei':str(fee),
        'frontierBlockSubsidyWei':str(5*10**18),
        'trustedBoundary':'historical root and transaction constants, Python execution and algorithm review; not a Lean MPT refinement proof',
    }

if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: independent-frontier-trie.py WITNESS.json')
    try:
        print(json.dumps(verify_historical(json.load(open(sys.argv[1], encoding='utf8')))))
    except (ValueError, AssertionError, TypeError, KeyError) as exc:
        print('Independent Frontier proof/replay rejected:',str(exc),file=sys.stderr)
        raise SystemExit(1)
