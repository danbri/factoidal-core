#!/usr/bin/env python3
"""Test the compiled SSZ byte-proof executable with an independent Python oracle.

Ordinary proof cases use complete trees constructed from deterministic chunks.
Expected roots exist before the proof is extracted. Deep boundary cases use
the same tree model with all-zero subtrees represented by their precomputed
roots. hashlib is used only in this test harness.

The local API refuses a wrong-width expected root with chunk_width. In the
pinned SSZ verification.py, a wrong-width expected root compares false.
"""

import argparse
import asyncio
from collections import Counter, defaultdict
from dataclasses import dataclass
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryFile
from time import perf_counter_ns


SSZ_COMMIT = "4c2f08805080c6b4b12ede7bf48ad6a80229f4b1"
SSZ_BLOBS = {
    "src/ssz/gindex.py": "e520ac9f89b2eb114174a0c83bf7e6187ef40304",
    "src/ssz/proofs.py": "ed6c558390d2f5ca2b66d875089095dfc9b19a6e",
    "src/ssz/verification.py": "70fc895a596f600d4df18569043c3d180fb87a4d",
}
SSZ_REPOSITORY = "https://github.com/ethereum/ssz-specs"
SHA_STANDARD = "https://doi.org/10.6028/NIST.FIPS.180-4"
SHA_EXAMPLES = "https://www.nist.gov/itl/ai/ai-standards-and-guidelines-group/nsrl-test-data"
SHA_ADDITIONAL_EXAMPLES = (
    "https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/"
    "documents/examples/SHA2_Additional.pdf"
)
NORMATIVE_SOURCES = {
    "ssz_repository": SSZ_REPOSITORY,
    "ssz_commit": SSZ_COMMIT,
    "ssz_git_blobs": SSZ_BLOBS,
    "sha256_standard": SHA_STANDARD,
    "sha256_examples": [SHA_EXAMPLES, SHA_ADDITIONAL_EXAMPLES],
}
CHUNK_BYTES = 32
MAX_HASH_BYTES = 65_536
MAX_DEPTH = 64
MAX_CLAIMS = 64
MAX_LINE_BYTES = 1_048_576
MAX_NUMBER_DIGITS = 128
MAX_JSON_NESTING = 2
LIMITS = {
    "chunk_bytes": CHUNK_BYTES,
    "max_claims": MAX_CLAIMS,
    "max_depth": MAX_DEPTH,
    "max_hash_input_bytes": MAX_HASH_BYTES,
    "max_jsonl_payload_bytes": MAX_LINE_BYTES,
    "max_json_number_digits": MAX_NUMBER_DIGITS,
    "max_json_nesting": MAX_JSON_NESTING,
}
DIGEST = re.compile(r"[0-9a-f]{64}")
ZERO_CHUNK = bytes(CHUNK_BYTES)
DEFAULT_BINARY = (
    Path(__file__).resolve().parents[1] / ".lake" / "build" / "bin" / "ssz-byte-proofs"
)


class CheckFailed(Exception):
    """A corpus check or an executable result failed."""


def require(condition, message):
    if not condition:
        raise CheckFailed(message)


def canonical(value):
    return json.dumps(value, separators=(",", ":"), sort_keys=True, allow_nan=False).encode()


def sha(data):
    return sha256(data).digest()


def pair(left, right):
    return sha(left + right)


def sample_bytes(domain, number, size):
    """Generate repeatable binary content without depending on a PRNG version."""
    prefix = f"factoidal-ssz-byte-proofs/{domain}/{number}/".encode()
    blocks = (sha(prefix + str(i).encode()) for i in range((size + 31) // 32))
    return b"".join(blocks)[:size]


def flip_first_bit(value):
    return bytes([value[0] ^ 1]) + value[1:]


def materialised_tree(depth, seed):
    """Return a complete tree indexed in breadth-first order with the root at 1."""
    width = 1 << depth
    nodes = [b""] * width
    nodes.extend(sample_bytes(f"tree-{seed}", i, CHUNK_BYTES) for i in range(width))
    for index in range(width - 1, 0, -1):
        nodes[index] = pair(nodes[2 * index], nodes[2 * index + 1])
    return nodes


class ZeroPaddedTree:
    """Represent a deep complete tree using roots for uniform zero subtrees."""

    def __init__(self, depth, leaves):
        self.depth = depth
        self.zero_roots = [ZERO_CHUNK]
        for _ in range(depth):
            root = self.zero_roots[-1]
            self.zero_roots.append(pair(root, root))
        self.nodes = dict(leaves)
        self.populate(1, depth, self.nodes.copy())

    def populate(self, index, remaining, leaves):
        if not leaves:
            return self.zero_roots[remaining]
        if remaining == 0:
            return leaves[index]
        mask = 1 << (remaining - 1)
        left = {leaf: data for leaf, data in leaves.items() if not leaf & mask}
        right = {leaf: data for leaf, data in leaves.items() if leaf & mask}
        value = pair(
            self.populate(index * 2, remaining - 1, left),
            self.populate(index * 2 + 1, remaining - 1, right),
        )
        self.nodes[index] = value
        return value

    def __getitem__(self, index):
        height = self.depth - (index.bit_length() - 1)
        return self.nodes.get(index, self.zero_roots[height])


def radix_path(index):
    return f"{index:b}"[1:]


def branch_indices(index):
    # Follow the claimed path from the root and record the unused side at each
    # fork. The wire representation puts the deepest witness first.
    parent = 1
    witnesses = []
    for turn in radix_path(index):
        child = parent * 2
        witnesses.append(child + (turn == "0"))
        parent = child + (turn == "1")
    return list(reversed(witnesses))


def branch_nodes(tree, index):
    return [tree[sibling] for sibling in branch_indices(index)]


def root_after(tree, updates):
    """Replace specified subtrees and hash their parents from the root down."""
    paths = {radix_path(index): value for index, value in updates.items()}

    def subtree(index, prefix, changed_paths):
        if not changed_paths:
            return tree[index]
        if prefix in changed_paths:
            require(len(changed_paths) == 1, "overlapping subtree updates in fixture")
            return paths[prefix]
        left = prefix + "0"
        right = prefix + "1"
        return pair(
            subtree(index * 2, left, [path for path in changed_paths if path.startswith(left)]),
            subtree(index * 2 + 1, right, [path for path in changed_paths if path.startswith(right)]),
        )

    root = subtree(1, "", list(paths))
    require(root != tree[1], "tampering fixture needs a different computed root")
    return root


def helper_indices(claims):
    """Find the unexplored subtree frontier by traversing the claim trie."""
    paths = tuple(radix_path(index) for index in claims)

    def unexplored(index, suffixes):
        if not suffixes:
            return [index]
        if "" in suffixes:
            require(suffixes == ("",), f"related indices in fixture: {claims}")
            return []
        return unexplored(
            2 * index, tuple(suffix[1:] for suffix in suffixes if suffix[0] == "0")
        ) + unexplored(
            2 * index + 1, tuple(suffix[1:] for suffix in suffixes if suffix[0] == "1")
        )

    require(claims and all(index > 1 for index in claims), f"bad fixture indices: {claims}")
    return sorted(unexplored(1, paths), reverse=True)


def multiproof_nodes(tree, claims):
    return [tree[index] for index in helper_indices(claims)]


@dataclass(frozen=True)
class Case:
    kind: str
    label: str
    request: dict | str
    expected: dict

    def wire(self):
        if isinstance(self.request, str):
            return self.request.encode() + b"\n"
        return canonical(self.request) + b"\n"


def hash_case(label, data, answer=None, failure=None):
    request = {"op": "hash", "data": data.hex()}
    result = {"status": "ok", "digest": answer or sha(data).hex()} if failure is None else error(failure)
    return Case("hash", label, request, result)


def error(code):
    return {"status": "error", "error": code}


def proof_result(root, calculated, failure):
    if failure is not None:
        return error(failure)
    result = root if calculated is None else calculated
    return {"status": "ok", "root": result.hex(), "matches": result == root}


def branch_case(label, index, leaf, proof, root, calculated=None, failure=None, **limits):
    request = {
        "op": "branch", "index": index, "leaf": leaf.hex(),
        "proof": [value.hex() for value in proof], "root": root.hex(), **limits,
    }
    return Case("branch", label, request, proof_result(root, calculated, failure))


def multi_case(label, indices, leaves, proof, root, calculated=None, failure=None, **limits):
    request = {
        "op": "multi", "indices": indices, "leaves": [value.hex() for value in leaves],
        "proof": [value.hex() for value in proof], "root": root.hex(), **limits,
    }
    return Case("multi", label, request, proof_result(root, calculated, failure))


def hash_cases():
    # Literal known answers check both hashlib and the executable.
    known_answers = (
        ("empty", b"", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
        ("nist-abc", b"abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
        (
            "nist-448-bit",
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
        (
            "nist-55-zero-bytes",
            bytes(55),
            "02779466cdec163811d078815c633f21901413081449002f24aa3e80f0b88ef7",
        ),
        (
            "nist-56-zero-bytes",
            bytes(56),
            "d4817aa5497628e7c77e6b606107042bbba3130888c5f47a375e6179be789fbb",
        ),
        (
            "nist-57-zero-bytes",
            bytes(57),
            "65a16cb7861335d5ace3c60718b5052e44660726da4cd13bb745381b235a1785",
        ),
        (
            "nist-64-zero-bytes",
            bytes(64),
            "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b",
        ),
        (
            "leading-zero-digest",
            bytes.fromhex("0001fa08"),
            "000041165a1568e9818c6c74394c0dfb942cfc28b23fdca03a467235ffa1de5e",
        ),
    )
    for label, message, answer in known_answers:
        require(sha(message).hex() == answer, f"hashlib failed known answer {label}")
        yield hash_case(label, message, answer)

    lengths = {
        size
        for boundary in (32, 56, 64, 120, 128, 184, 192, 248, 256, 512, 1024, MAX_HASH_BYTES)
        for size in range(boundary - 2, boundary + 3)
        if size <= MAX_HASH_BYTES
    }
    for size in sorted(lengths):
        yield hash_case(
            "sha-input-at-limit" if size == MAX_HASH_BYTES else f"sha-padding-{size}",
            sample_bytes("sha-padding", size, size),
        )
    for i in range(64):
        size = (i * 101 + 3) % (min(MAX_HASH_BYTES, 512) + 1)
        yield hash_case("sha-binary", sample_bytes("sha-binary", i, size))

    yield hash_case(
        "sha-input-over-limit",
        sample_bytes("sha-padding", MAX_HASH_BYTES + 1, MAX_HASH_BYTES + 1),
        failure="resource_limit",
    )


def pair_orientation_cases():
    for i in range(24):
        left = sample_bytes("pair-left", i, CHUNK_BYTES)
        right = sample_bytes("pair-right", i, CHUNK_BYTES)
        root = pair(left, right)
        reversed_root = pair(right, left)
        require(root != reversed_root, "pair orientation fixture collided")
        yield branch_case("pair-left-child", 2, left, [right], root)
        yield branch_case("pair-right-child", 3, right, [left], root)
        yield branch_case("pair-reversed-child-order", 2, right, [left], root, reversed_root)

    yield branch_case("pair-all-zero", 2, ZERO_CHUNK, [ZERO_CHUNK], pair(ZERO_CHUNK, ZERO_CHUNK))
    data = sample_bytes("pair-split", 0, 64)
    left, right = data[:32], data[32:]
    root = sha(data)
    # The concatenated bytes match an admitted pair exactly.
    yield branch_case("bad-31-33-split", 2, left[:-1], [left[-1:] + right], root, failure="chunk_width")
    yield branch_case("bad-33-31-split", 2, left + right[:1], [right[1:]], root, failure="chunk_width")


def branch_and_multiproof_cases():
    for i in range(128):
        depth = 3 + i % 5
        tree = materialised_tree(depth, i)
        width = 1 << depth
        root = tree[1]
        index = width + (i * 13 + i // 5) % width
        leaf = tree[index]
        proof = branch_nodes(tree, index)
        changed_leaf = flip_first_bit(leaf)
        changed_witness = flip_first_bit(proof[0])
        yield branch_case("branch-valid", index, leaf, proof, root)
        yield branch_case(
            "branch-leaf-tampered", index, changed_leaf, proof, root,
            root_after(tree, {index: changed_leaf}),
        )
        yield branch_case(
            "branch-witness-tampered", index, leaf, [changed_witness, *proof[1:]], root,
            root_after(tree, {branch_indices(index)[0]: changed_witness}),
        )
        yield branch_case("branch-root-tampered", index, leaf, proof, flip_first_bit(root), root)

        first = (i * 17 + 3) % width
        claims = [width + first, width + (first + 2) % width, width + (first + 5) % width]
        nodes = [tree[claim] for claim in claims]
        proof = multiproof_nodes(tree, claims)
        yield multi_case("same-depth-claims", claims, nodes, proof, root)
        yield multi_case("reordered-claims-with-paired-nodes", claims[::-1], nodes[::-1], proof, root)
        changed_leaf = flip_first_bit(nodes[0])
        changed_witness = flip_first_bit(proof[0])
        yield multi_case(
            "multiproof-leaf-tampered", claims, [changed_leaf, *nodes[1:]], proof, root,
            root_after(tree, {claims[0]: changed_leaf}),
        )
        yield multi_case(
            "multiproof-witness-tampered", claims, nodes, [changed_witness, *proof[1:]], root,
            root_after(tree, {helper_indices(claims)[0]: changed_witness}),
        )
        yield multi_case("multiproof-root-tampered", claims, nodes, proof, flip_first_bit(root), root)

        # The first claim covers all of the left subtree. In the right half,
        # these two claims select disjoint subtrees at two further depths.
        mixed = [2, 6 + i % 2, width + (3 - i % 2) * (width // 4) + i % (width // 4)]
        yield multi_case(
            "mixed-depth-claims", mixed, [tree[claim] for claim in mixed],
            multiproof_nodes(tree, mixed), root,
        )


def exhaustive_depth_three_cases():
    tree = materialised_tree(3, 132)

    def antichains(index):
        if index >= 8:
            return [(), (index,)]
        # Claim the current node, or combine independent choices in its children.
        return [(index,)] + [
            left + right for left, right in product(antichains(2 * index), antichains(2 * index + 1))
        ]

    topologies = [left + right for left, right in product(antichains(2), antichains(3)) if left or right]
    require(len(topologies) == len(set(topologies)) == 675, "incomplete depth-three antichains")
    require(sum(map(len, topologies)) == 2652, "incomplete depth-three tampering cases")

    for topology in topologies:
        claims = list(topology)
        nodes = [tree[index] for index in claims]
        proof = multiproof_nodes(tree, claims)
        root = tree[1]
        yield multi_case("exhaustive-depth-three-original", claims, nodes, proof, root)
        yield multi_case("exhaustive-depth-three-reversed", claims[::-1], nodes[::-1], proof, root)
        for position, index in enumerate(claims):
            changed_node = flip_first_bit(nodes[position])
            changed_nodes = nodes.copy()
            changed_nodes[position] = changed_node
            yield multi_case(
                "exhaustive-depth-three-tampered-claim", claims, changed_nodes, proof, root,
                root_after(tree, {index: changed_node}),
            )


def proof_edge_cases():
    tree = materialised_tree(3, 128)
    root = tree[1]
    index, leaf = 10, tree[10]
    branch = branch_nodes(tree, index)
    require(len(set(branch)) == len(branch), "branch order fixture has equal witnesses")
    yield branch_case("branch-index-zero", 0, leaf, [], leaf, failure="invalid_index")
    yield branch_case("branch-index-root", 1, leaf, [], leaf, failure="invalid_index")
    yield branch_case("branch-left-child", 2, tree[2], [tree[3]], root)
    yield branch_case("branch-right-child", 3, tree[3], [tree[2]], root)
    yield branch_case("branch-short-witness", index, leaf, branch[:-1], root, failure="proof_length")
    yield branch_case("branch-long-witness", index, leaf, [*branch, ZERO_CHUNK], root, failure="proof_length")
    yield branch_case(
        "branch-reversed-witnesses", index, leaf, branch[::-1], root,
        root_after(tree, dict(zip(branch_indices(index), reversed(branch)))),
    )

    for width in (0, 31, 33):
        yield branch_case(f"branch-leaf-{width}-bytes", index, bytes(width), branch, root, failure="chunk_width")
        yield branch_case(
            f"branch-witness-{width}-bytes", index, leaf, [bytes(width), *branch[1:]], root, failure="chunk_width"
        )
        yield branch_case(f"branch-root-{width}-bytes", index, leaf, branch, bytes(width), failure="chunk_width")

    # A single branch with a root whose encoded digest begins with a zero byte.
    leading_zero_leaf = (3).to_bytes(CHUNK_BYTES, "big")
    leading_zero_root = pair(leading_zero_leaf, ZERO_CHUNK)
    require(leading_zero_root[0] == 0, "leading-zero pair fixture has changed")
    yield branch_case("branch-leading-zero-root", 2, leading_zero_leaf, [ZERO_CHUNK], leading_zero_root)

    siblings = [2, 3]
    siblings_proof = multiproof_nodes(tree, siblings)
    require(siblings_proof == [], "siblings must have no helper indices")
    yield multi_case("root-children-empty-helpers", siblings, [tree[2], tree[3]], siblings_proof, root)
    yield multi_case(
        "root-children-swapped-nodes", siblings, [tree[3], tree[2]], siblings_proof, root,
        root_after(tree, {2: tree[3], 3: tree[2]}),
    )
    yield multi_case(
        "multiproof-leading-zero-root", siblings, [leading_zero_leaf, ZERO_CHUNK], [], leading_zero_root
    )

    single = [index]
    yield multi_case("multiproof-single-claim", single, [leaf], multiproof_nodes(tree, single), root)

    claims = [5, 12]
    nodes = [tree[claim] for claim in claims]
    proof = multiproof_nodes(tree, claims)
    require(len(proof) > 1 and len(set(proof)) == len(proof), "multiproof order fixture lacks distinct helpers")
    yield multi_case("multiproof-empty-claims", [], [], [], root, failure="invalid_claims")
    yield multi_case("multiproof-index-zero", [0], [leaf], [], leaf, failure="invalid_claims")
    yield multi_case("multiproof-index-root", [1], [leaf], [], leaf, failure="invalid_claims")
    yield multi_case(
        "multiproof-duplicate-claims", [2, 2], [tree[2], tree[2]], [tree[3]], root, failure="invalid_claims",
    )
    for order in ([2, 4], [4, 2]):
        yield multi_case(
            "multiproof-nested-claims", order, [tree[claim] for claim in order], [tree[3], tree[5]],
            root, failure="invalid_claims",
        )
    yield multi_case("multiproof-short-leaves", claims, nodes[:-1], proof, root, failure="leaf_count")
    yield multi_case("multiproof-long-leaves", claims, [*nodes, ZERO_CHUNK], proof, root, failure="leaf_count")
    yield multi_case("multiproof-short-witness", claims, nodes, proof[:-1], root, failure="proof_length")
    yield multi_case("multiproof-long-witness", claims, nodes, [*proof, ZERO_CHUNK], root, failure="proof_length")
    yield multi_case(
        "multiproof-reversed-witnesses", claims, nodes, proof[::-1], root,
        root_after(tree, dict(zip(helper_indices(claims), reversed(proof)))),
    )

    for width in (0, 31, 33):
        yield multi_case(
            f"multiproof-leaf-{width}-bytes", claims, [bytes(width), nodes[1]], proof, root, failure="chunk_width"
        )
        yield multi_case(
            f"multiproof-witness-{width}-bytes", claims, nodes, [bytes(width), *proof[1:]],
            root, failure="chunk_width",
        )
        yield multi_case(
            f"multiproof-root-{width}-bytes", claims, nodes, proof, bytes(width), failure="chunk_width",
        )


def bound_cases():
    small = materialised_tree(3, 129)
    branch = (11, small[11], branch_nodes(small, 11), small[1])
    yield branch_case("branch-configured-depth-exact", *branch, maxDepth=3)
    yield branch_case("branch-configured-depth-exceeded", *branch, maxDepth=2, failure="resource_limit")
    yield branch_case("branch-configured-depth-zero", *branch, maxDepth=0, failure="resource_limit")
    yield branch_case(
        "branch-configured-depth-over-limit", *branch, maxDepth=MAX_DEPTH + 1, failure="resource_limit"
    )

    small_claims = [2, 12]
    small_proof = (
        small_claims, [small[index] for index in small_claims], multiproof_nodes(small, small_claims), small[1],
    )
    yield multi_case("multiproof-configured-bounds-exact", *small_proof, maxClaims=2, maxDepth=3)
    yield multi_case("multiproof-configured-depth-exceeded", *small_proof, maxDepth=2, failure="resource_limit")
    yield multi_case("multiproof-configured-depth-zero", *small_proof, maxDepth=0, failure="resource_limit")
    yield multi_case(
        "multiproof-configured-depth-over-limit", *small_proof, maxDepth=MAX_DEPTH + 1, failure="resource_limit"
    )
    yield multi_case("multiproof-configured-claims-exceeded", *small_proof, maxClaims=1, failure="resource_limit")
    yield multi_case("multiproof-configured-claims-zero", *small_proof, maxClaims=0, failure="resource_limit")
    yield multi_case(
        "multiproof-configured-claims-over-limit", *small_proof, maxClaims=MAX_CLAIMS + 1, failure="resource_limit"
    )

    all_leaves = list(range(MAX_CLAIMS, 2 * MAX_CLAIMS))
    tree = materialised_tree(MAX_CLAIMS.bit_length() - 1, 130)
    proof = multiproof_nodes(tree, all_leaves)
    require(not proof, "all leaves must cover the entire tree")
    yield multi_case("all-leaf-multiproof-at-claim-limit", all_leaves, tree[MAX_CLAIMS:], proof, tree[1])
    tree = materialised_tree(MAX_CLAIMS.bit_length(), 131)
    too_many = list(range(2 * MAX_CLAIMS, 3 * MAX_CLAIMS + 1))
    yield multi_case(
        "multiproof-claim-count-over-limit", too_many, [tree[index] for index in too_many],
        multiproof_nodes(tree, too_many), tree[1], failure="resource_limit",
    )

    positions = [(1 << MAX_DEPTH) | (i << (MAX_DEPTH - 6)) for i in range(MAX_CLAIMS)]
    positions[-1] = (1 << (MAX_DEPTH + 1)) - 1
    deep = ZeroPaddedTree(
        MAX_DEPTH, {index: sample_bytes("deep-leaf", i, CHUNK_BYTES) for i, index in enumerate(positions)}
    )
    for index in (positions[0], positions[-1]):
        yield branch_case(
            "branch-index-at-max-depth", index, deep[index], branch_nodes(deep, index),
            deep[1], maxDepth=MAX_DEPTH,
        )
    deep_proof = multiproof_nodes(deep, positions)
    require(len(deep_proof) == MAX_CLAIMS * (MAX_DEPTH - 6), "deep fixture must separate all 64 paths")
    yield multi_case(
        "multiproof-at-claim-and-depth-limits", positions, [deep[index] for index in positions], deep_proof,
        deep[1], maxClaims=MAX_CLAIMS, maxDepth=MAX_DEPTH,
    )

    too_deep = 1 << (MAX_DEPTH + 1)
    tree = ZeroPaddedTree(MAX_DEPTH + 1, {too_deep: sample_bytes("too-deep", 0, CHUNK_BYTES)})
    proof = branch_nodes(tree, too_deep)
    yield branch_case(
        "branch-index-over-max-depth", too_deep, tree[too_deep], proof, tree[1], failure="resource_limit"
    )
    yield multi_case(
        "multiproof-index-over-max-depth", [too_deep], [tree[too_deep]], proof, tree[1],
        failure="resource_limit",
    )


def wire_cases():
    valid_hash = hash_case("hash-after-parse-errors", b"wire recovery")
    for label, payload in (
        ("blank-line", ""),
        ("invalid-json", "{"),
        ("non-object-request", "[]"),
        ("unknown-operation", '{"op":"nonesuch"}'),
        ("missing-data", '{"op":"hash"}'),
        ("nonstring-data", '{"op":"hash","data":12}'),
        ("odd-length-hex", '{"op":"hash","data":"abc"}'),
        ("bad-hex-digit", '{"op":"hash","data":"na"}'),
        ("unknown-field", '{"op":"hash","data":"00","unknown":1}'),
        ("exponent-expansion", '{"op":"hash","data":1e999999999999999999}'),
        ("negative-exponent-expansion", '{"op":"hash","data":1E-999999999999999999}'),
        ("array-nesting-above-limit", '{"op":"hash","data":[[]]}'),
        ("object-nesting-above-limit", '{"op":"hash","data":{"a":{"b":1}}}'),
        ("number-lexeme-at-digit-limit", '{"op":"hash","data":' + "9" * MAX_NUMBER_DIGITS + "}"),
    ):
        yield Case("wire", label, payload, error("parse_error"))

    yield Case(
        "wire", "number-lexeme-above-digit-limit",
        '{"op":"hash","data":' + "9" * (MAX_NUMBER_DIGITS + 1) + "}",
        error("resource_limit"),
    )
    yield hash_case("long-digit-sequence-quoted-as-hex", b"\x99" * (MAX_NUMBER_DIGITS // 2 + 1))

    root = pair(ZERO_CHUNK, ZERO_CHUNK)
    valid_branch = branch_case("valid-wire-branch", 2, ZERO_CHUNK, [ZERO_CHUNK], root)
    branch_json = canonical(valid_branch.request).decode()
    escaped_index = r'"\u0069ndex"'
    yield Case(
        "wire", "duplicate-index-field", '{"index":1,' + branch_json[1:], error("parse_error"),
    )
    yield Case(
        "wire", "duplicate-escaped-index-field", branch_json[:-1] + "," + escaped_index + ":2}",
        error("parse_error"),
    )
    yield Case(
        "wire", "single-escaped-index-field", branch_json.replace('"index"', escaped_index), valid_branch.expected,
    )
    for label, fields in (
        ("negative-index", {"index": -1}),
        ("fractional-index", {"index": 2.5}),
        ("noninteger-index", {"index": "2"}),
        ("boolean-index", {"index": True}),
        ("nonarray-proof", {"proof": ""}),
        ("invalid-witness-hex", {"proof": ["ZZ"]}),
        ("invalid-root-hex", {"root": "x0"}),
        ("negative-depth-cap", {"maxDepth": -1}),
    ):
        yield Case("wire", label, {**valid_branch.request, **fields}, error("parse_error"))
    yield valid_hash

    request = canonical(valid_hash.request).decode()
    at_limit = " " * (MAX_LINE_BYTES - len(request)) + request
    for suffix, spelling in (("", "lf"), ("\r", "crlf")):
        yield Case("wire", f"json-payload-at-line-limit-{spelling}", at_limit + suffix, valid_hash.expected)
        yield Case(
            "wire", f"json-payload-over-line-limit-{spelling}", " " + at_limit + suffix, error("resource_limit"),
        )
    yield hash_case("hash-after-line-overflow", b"line overflow recovery")


def corpus():
    cases = [
        *hash_cases(),
        *pair_orientation_cases(),
        *branch_and_multiproof_cases(),
        *exhaustive_depth_three_cases(),
        *proof_edge_cases(),
        *bound_cases(),
        *wire_cases(),
    ]
    require(helper_indices([4, 6]) == [7, 5], "unexpected helper indices for [4, 6]")
    require(helper_indices([4]) == branch_indices(4) == [5, 3], "unexpected witness order for [4]")
    require(sum(case.kind in ("branch", "multi") for case in cases) >= 1024, "proof corpus is too small")
    return cases


ERROR_CODES = {
    "resource_limit", "invalid_index", "invalid_claims", "leaf_count", "proof_length",
    "chunk_width", "incomplete_proof", "conflicting_node", "parse_error",
}


def unique_object(fields):
    result = {}
    for key, value in fields:
        require(key not in result, f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def decode_json(payload):
    try:
        return json.loads(payload.decode("utf-8"), object_pairs_hook=unique_object)
    except ValueError as exc:
        raise CheckFailed(f"malformed JSON: {exc}") from exc


def is_digest(value):
    return isinstance(value, str) and DIGEST.fullmatch(value) is not None


def decode_response(payload):
    require(payload, "empty executable output before the expected response")
    require(payload.endswith(b"\n"), "unterminated executable output row")
    value = decode_json(payload)
    require(isinstance(value, dict), "executable response must be an object")
    if value.get("status") == "error":
        require(
            value.keys() == {"status", "error"}
            and isinstance(value["error"], str) and value["error"] in ERROR_CODES,
            f"bad error response: {value!r}",
        )
    elif value.get("status") == "ok" and "digest" in value:
        require(
            value.keys() == {"status", "digest"} and is_digest(value["digest"]),
            f"bad digest response: {value!r}",
        )
    else:
        require(
            value.get("status") == "ok" and value.keys() == {"status", "root", "matches"}
            and type(value["matches"]) is bool and is_digest(value["root"]),
            f"bad proof response: {value!r}",
        )
    return value


def compare_response(case, output):
    actual = decode_response(output)
    require(actual == case.expected, f"expected {case.expected!r}, received {actual!r}")


def check_mutations(cases):
    def fixture(label):
        return next(case for case in cases if case.label == label)

    valid = fixture("branch-valid")
    mismatch = fixture("branch-root-tampered")
    invalid = fixture("branch-index-root")
    digest = fixture("leading-zero-digest")
    def result_line(case, **changes):
        return canonical({**case.expected, **changes}) + b"\n"

    forged = "ab" * CHUNK_BYTES
    mutations = {
        "forged-acceptance-of-mismatched-root": (mismatch, result_line(mismatch, matches=True)),
        "forged-acceptance-of-invalid-index": (invalid, result_line(valid)),
        "forged-cryptographic-digest": (digest, result_line(digest, digest=forged)),
        "forged-computed-root": (valid, result_line(valid, root=forged)),
        "forged-error-code": (invalid, result_line(invalid, error="parse_error")),
        "dropped-leading-zero-digest": (digest, result_line(digest, digest=digest.expected["digest"].lstrip("0"))),
        "empty-output": (valid, b""),
        "blank-output-record": (valid, b"\n"),
        "malformed-output-json": (valid, b"{\n"),
        "truncated-output-record": (valid, canonical(valid.expected)),
        "duplicate-output-field": (invalid, b'{"status":"ok","status":"error","error":"invalid_index"}\n'),
        "integer-encoded-as-boolean": (valid, result_line(valid, matches=1)),
    }
    for label, (case, payload) in mutations.items():
        compare_response(case, canonical(case.expected) + b"\n")
        try:
            compare_response(case, payload)
        except CheckFailed:
            continue
        raise CheckFailed(f"comparator accepted mutation {label}")
    return list(mutations)


async def exchange(executable, cases, requests):
    samples = []
    output_digest = sha256()
    with TemporaryFile() as stderr:
        child = await asyncio.create_subprocess_exec(
            str(executable), stdin=asyncio.subprocess.PIPE, stdout=asyncio.subprocess.PIPE, stderr=stderr,
        )
        try:
            for number, (case, request) in enumerate(zip(cases, requests, strict=True), start=1):
                try:
                    begin = perf_counter_ns()
                    child.stdin.write(request)
                    await child.stdin.drain()
                    output = await child.stdout.readline()
                    samples.append(perf_counter_ns() - begin)
                    compare_response(case, output)
                    output_digest.update(output)
                except (ValueError, ConnectionError, CheckFailed) as exc:
                    raise CheckFailed(f"row {number}, {case.label}: {exc}") from exc
            child.stdin.close()
            require(not await child.stdout.read(1), "unexpected extra executable output after the last row")
            returncode = await child.wait()
            stderr.seek(0)
            diagnostic = stderr.read(4096).decode("utf-8", errors="replace").strip()
            require(returncode == 0, f"executable exited with code {returncode}: {diagnostic}")
            require(not diagnostic, f"unexpected executable stderr: {diagnostic}")
        finally:
            if child.returncode is None:
                try:
                    child.kill()
                except ProcessLookupError:
                    pass
                await child.communicate()
    return samples, output_digest.hexdigest()


def corpus_digests(cases, requests):
    test_digest = sha256()
    input_digest = sha256()
    for case, request in zip(cases, requests, strict=True):
        input_digest.update(request)
        test_digest.update(canonical({
            "kind": case.kind, "label": case.label,
            "wire": request.decode("utf-8"), "expected": case.expected,
        }) + b"\n")
    return test_digest.hexdigest(), input_digest.hexdigest()


def outcome(case):
    value = case.expected
    if value["status"] == "error":
        return value["error"]
    if "digest" in value:
        return "digest"
    return "matched" if value["matches"] else "mismatched"


def timing_summary(samples):
    ordered = sorted(samples)
    return {
        "count": len(ordered),
        **{f"p{p}": ordered[(p * len(ordered) + 99) // 100 - 1] for p in (50, 95, 99)},
        "max": ordered[-1],
    }


def counts(cases):
    by_kind = defaultdict(Counter)
    for case in cases:
        by_kind[case.kind][outcome(case)] += 1
    return {
        "rows": len(cases),
        "by_kind_and_result": dict(by_kind),
        "by_label": dict(Counter(case.label for case in cases)),
        "matched_without_helpers": sum(
            case.kind == "multi" and not case.request["proof"] and outcome(case) == "matched"
            for case in cases
        ),
    }


def file_digest(path):
    result = sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            result.update(block)
    return result.hexdigest()


def timing_report(cases, samples):
    timings = defaultdict(list)
    for case, sample in zip(cases, samples, strict=True):
        timings[case.kind].append(sample)
    return {
        "unit": "ns",
        "scope": "single-request JSONL pipe round trip in one executable process",
        "samples_ns": samples,
        "first_request_ns": samples[0],
        "all": timing_summary(samples),
        "by_kind": {kind: timing_summary(latencies) for kind, latencies in timings.items()},
    }


def make_report(executable, cases, requests, samples, output_digest, controls):
    corpus_digest, input_digest = corpus_digests(cases, requests)
    return {
        "schema": "factoidal.ssz-byte-proofs.test-report.v1",
        "result": "pass",
        "counts": counts(cases),
        "limits": LIMITS,
        "sources": {
            **NORMATIVE_SOURCES,
            "checker_sha256": file_digest(Path(__file__)),
            "executable_sha256": file_digest(executable),
        },
        "corpus_sha256": corpus_digest,
        "request_stream_sha256": input_digest,
        "response_stream_sha256": output_digest,
        "mutation_controls_detected": controls,
        "timing": timing_report(cases, samples),
        "python_version": sys.version.split()[0],
    }


def validate_report(report, cases, controls):
    fields = {
        "schema", "result", "counts", "limits", "sources", "corpus_sha256",
        "request_stream_sha256", "response_stream_sha256", "mutation_controls_detected",
        "timing", "python_version",
    }
    require(isinstance(report, dict) and report.keys() == fields, "bad report fields")
    require(report["schema"] == "factoidal.ssz-byte-proofs.test-report.v1", "bad report schema")
    require(report["result"] == "pass" and report["counts"] == counts(cases), "bad report result or row counts")
    require(report["limits"] == LIMITS, "bad report limits")
    for field in ("corpus_sha256", "request_stream_sha256", "response_stream_sha256"):
        require(is_digest(report[field]), f"bad {field}")
    sources = report["sources"]
    digest_fields = {"checker_sha256", "executable_sha256"}
    require(
        isinstance(sources, dict) and sources.keys() == NORMATIVE_SOURCES.keys() | digest_fields,
        "bad report source fields",
    )
    for field in digest_fields:
        require(is_digest(sources[field]), f"bad {field}")
    require(all(sources[name] == value for name, value in NORMATIVE_SOURCES.items()), "bad source pins")
    require(report["mutation_controls_detected"] == controls, "bad mutation control counts")
    timing = report["timing"]
    require(isinstance(timing, dict), "bad timing fields")
    samples = timing.get("samples_ns")
    require(isinstance(samples, list) and len(samples) == len(cases), "bad timing sample count")
    require(all(type(value) is int and value >= 0 for value in samples), "bad timing measurement")
    try:
        measured = canonical(timing)
    except ValueError as exc:
        raise CheckFailed("malformed timing report") from exc
    require(measured == canonical(timing_report(cases, samples)), "bad timing summary")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path, nargs="?", default=DEFAULT_BINARY)
    parser.add_argument("--report", type=Path, help="write the complete JSON test report to this path")
    parser.add_argument("--timeout", type=int, default=120, help="whole-exchange deadline in seconds")
    parser.add_argument(
        "--self-test", action="store_true", help="check the corpus and comparator without running Lean",
    )
    args = parser.parse_args()
    if args.timeout < 1:
        parser.error("--timeout must be positive")
    if args.self_test and args.report:
        parser.error("--report requires an actual executable run")

    try:
        cases = corpus()
        requests = [case.wire() for case in cases]
        controls = check_mutations(cases)
        if args.self_test:
            for case in cases:
                compare_response(case, canonical(case.expected) + b"\n")
            print(
                f"SSZ byte-proof oracle self-test: {len(cases)} generated rows, "
                f"{len(controls)} comparator mutations detected, "
                f"corpus SHA-256 {corpus_digests(cases, requests)[0]}"
            )
            return 0

        binary = args.executable.resolve()
        samples, output_digest = asyncio.run(asyncio.wait_for(exchange(binary, cases, requests), args.timeout))
        report = make_report(binary, cases, requests, samples, output_digest, controls)
        encoded = (json.dumps(report, indent=2, sort_keys=True, allow_nan=False) + "\n").encode()
        validate_report(decode_json(encoded), cases, controls)
        if args.report:
            args.report.write_bytes(encoded)
        print(
            f"SSZ byte-proof differential check: {len(cases)} executable rows matched, "
            f"{len(controls)} comparator mutations detected, "
            f"corpus SHA-256 {report['corpus_sha256']}"
        )
        return 0
    except asyncio.TimeoutError:
        print(
            f"SSZ byte-proof check failed: executable exchange timed out after {args.timeout} s",
            file=sys.stderr,
        )
        return 1
    except (CheckFailed, OSError) as exc:
        print(f"SSZ byte-proof check failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
