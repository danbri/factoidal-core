# Mainnet London header-pair admission — 23 November 2026

Issue #850, parent #725 / #652. Base #847 at e45529b533514695e748aba8816c5caac1081c00. Independent Lean 4.33.1; no new external implementation packages. This slice derives the mainnet activation flag at 12,965,000, rejects non-adjacent numbers, non-increasing timestamps and unequal supplied parent hash words, then invokes the existing exact EIP-1559 header fee check. Earlier forks are indeterminate in this entry point. The hash words are numeric 256-bit commitments supplied by the caller, not computed from RLP. No canonical or authenticated parent selection is claimed.

Protocol reference: EIP-1559 https://eips.ethereum.org/EIPS/eip-1559 and the pinned London reference in docs/20261123-evm-london-header-fees.md. No third-party executable code used. Lean compiler and runtime, file transport, and authenticity of input remain trusted. The native batch CLI reads a file before checking record lengths, so a preallocation cap is still required before adversarial deployment.

The new theorem statements connect acceptance to the actual fee checker, the derived activation, link constraints, width refusal, earlier-fork refusal, and the inherited min-one-wei recurrence. Only actual printed axiom results count, and the new CI emits source blobs and exact axiom sets. Python produces 3,072 selected requests (1,536 originals and 1,536 mutations), plus malformed input and three negative comparison controls; no runtime decision uses Python. Commands (working directory formal/lean4/evm-cleanroom):

    lake -f lakefile-london-chain.toml build evm-header-chain
    lake -f lakefile-london-chain.toml env lean EVMCleanroom/HeaderChain.lean
    python3 scripts/check-london-chain.py .lake/build/bin/evm-header-chain

Source and tests are published for exact-head Linux checking; new compilation and oracle outcomes are not yet established. Existing London, EVM and Frontier gates must rerun; no performance, full premerge, independent expert review or node readiness claim. Not yet integrated with authenticated header RLP, execution block validation, or Engine API. No main merge.
