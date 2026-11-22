// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {RiscZeroGroth16Verifier} from "risc0-ethereum/src/groth16/RiscZeroGroth16Verifier.sol";
import {ControlID} from "risc0-ethereum/src/groth16/ControlID.sol";

/// @notice Verifies the exact Factoidal ASK v1 journal and requires an authorised true result.
/// @dev The application chooses image, policy and context independently of an untrusted receipt.
///      This reference deploys the pinned official verifier itself; it accepts no supplied verifier.
///      This is a view gate: an application performing an action must consume its own nonce/context.
///      The graph commitment does not establish provenance or authority of the committed data.
contract FactoidalAskGate {
    error InvalidConfiguration();
    error JournalLength(uint256 received);
    error SealLength(uint256 received);
    error NonCanonicalBoolean(uint256 received);
    error NotSatisfied();
    error PolicyMismatch(bytes32 received, bytes32 expected);
    error ContextMismatch(bytes32 received, bytes32 expected);

    RiscZeroGroth16Verifier public immutable verifier;
    bytes32 public immutable imageId;
    bytes32 public immutable authorisedPolicyHash;
    bytes32 public immutable authorisedContextHash;

    constructor(bytes32 trustedImageId, bytes32 policyHash, bytes32 contextHash) {
        if (trustedImageId == bytes32(0) || policyHash == bytes32(0) || contextHash == bytes32(0)) {
            revert InvalidConfiguration();
        }
        imageId = trustedImageId;
        authorisedPolicyHash = policyHash;
        authorisedContextHash = contextHash;
        verifier = new RiscZeroGroth16Verifier(ControlID.CONTROL_ROOT, ControlID.BN254_CONTROL_ID);
        // The patched 3.1 circuit/setup, not the superseded earlier 3.1 deployment.
        if (verifier.SELECTOR() != hex"e71e6620") revert InvalidConfiguration();
    }

    /// @return graphCommitment The commitment from the verified, authorised true statement.
    function verifyTrue(bytes calldata seal, bytes calldata journal) external view returns (bytes32) {
        if (journal.length != 128) revert JournalLength(journal.length);
        // Reading the final ABI word as uint256 lets us explicitly reject both malformed
        // Boolean encodings and a well-formed false result before the pairing check.
        (bytes32 graphCommitment, bytes32 policyHash, bytes32 contextHash, uint256 answer) =
            abi.decode(journal, (bytes32, bytes32, bytes32, uint256));
        if (answer > 1) revert NonCanonicalBoolean(answer);
        if (answer == 0) revert NotSatisfied();
        if (policyHash != authorisedPolicyHash) revert PolicyMismatch(policyHash, authorisedPolicyHash);
        if (contextHash != authorisedContextHash) revert ContextMismatch(contextHash, authorisedContextHash);
        if (seal.length != 260) revert SealLength(seal.length);
        verifier.verify(seal, imageId, sha256(journal));
        return graphCommitment;
    }
}
