// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {Test} from "forge-std/Test.sol";
import {VerificationFailed} from "risc0-ethereum/src/IRiscZeroVerifier.sol";
import {FactoidalAskGate} from "../src/FactoidalAskGate.sol";

/// @dev Deliberately fails setup when a real ASK receipt or independently
///      authorised statement is absent. It never substitutes a mock or skips.
contract RealAskReceiptTest is Test {
    FactoidalAskGate internal gate;
    bytes internal seal;
    bytes internal journal;
    bytes32 internal expectedImage;
    bytes32 internal expectedGraph;
    bytes32 internal expectedPolicy;
    bytes32 internal expectedContext;

    function setUp() public {
        string memory directory = vm.envOr("FACTOIDAL_EVM_FIXTURE_DIR", string("fixtures"));
        bytes memory selected = bytes(directory);
        if (keccak256(selected) != keccak256(bytes("fixtures"))) {
            bytes memory prefix = bytes("fixtures/");
            require(selected.length > prefix.length, "expected fixtures or a named child directory");
            for (uint256 i; i < prefix.length; ++i) {
                require(selected[i] == prefix[i], "fixture directory must be within fixtures");
            }
            for (uint256 i = prefix.length; i < selected.length; ++i) {
                uint8 c = uint8(selected[i]);
                require(
                    (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122)
                        || c == 45 || c == 95,
                    "fixture child name permits only letters, digits, hyphens and underscores"
                );
            }
        }
        string memory expected = vm.readFile(string.concat(directory, "/expected-statement.json"));
        expectedImage = vm.parseJsonBytes32(expected, ".imageId");
        bytes memory expectedJournal = vm.parseJsonBytes(expected, ".journal");
        require(expectedJournal.length == 128, "expected journal must have 128 bytes");
        uint256 answer;
        (expectedGraph, expectedPolicy, expectedContext, answer) =
            abi.decode(expectedJournal, (bytes32, bytes32, bytes32, uint256));
        require(answer == 1, "expected statement must authorise true");
        gate = new FactoidalAskGate(expectedImage, expectedPolicy, expectedContext);

        string memory proof = vm.readFile(string.concat(directory, "/ask-proof.json"));
        require(vm.parseJsonBytes32(proof, ".imageId") == expectedImage, "proof image differs");
        seal = vm.parseJsonBytes(proof, ".seal");
        journal = vm.parseJsonBytes(proof, ".journal");
        assertEq(journal, expectedJournal, "proof journal differs from authorised statement");
    }

    function testRealAskReceiptVerifies() public {
        bytes memory submittedSeal = seal;
        bytes memory submittedJournal = journal;
        address target = address(gate);
        uint256 beforeCall = gasleft();
        bytes32 verifiedGraph = FactoidalAskGate(target).verifyTrue(submittedSeal, submittedJournal);
        uint256 externalCallGas = beforeCall - gasleft();
        // Local successful external-call cost, including ABI/STATICCALL
        // overhead. This excludes deployment and transaction intrinsic gas.
        emit log_named_uint("verifyTrue external-call gas", externalCallGas);
        assertEq(verifiedGraph, expectedGraph);
    }

    function testRealAskReceiptRejectsChangedImage() public {
        FactoidalAskGate wrong =
            new FactoidalAskGate(expectedImage ^ bytes32(uint256(1)), expectedPolicy, expectedContext);
        vm.expectRevert(VerificationFailed.selector);
        wrong.verifyTrue(seal, journal);
    }

    function testRealAskReceiptRejectsChangedGraphCommitment() public {
        bytes memory changed = journal;
        changed[0] ^= bytes1(uint8(1));
        vm.expectRevert(VerificationFailed.selector);
        gate.verifyTrue(seal, changed);
    }

    function testRealAskReceiptRejectsUnauthorisedPolicy() public {
        bytes32 wrongPolicy = expectedPolicy ^ bytes32(uint256(1));
        FactoidalAskGate wrong = new FactoidalAskGate(expectedImage, wrongPolicy, expectedContext);
        vm.expectRevert(
            abi.encodeWithSelector(FactoidalAskGate.PolicyMismatch.selector, expectedPolicy, wrongPolicy)
        );
        wrong.verifyTrue(seal, journal);
    }

    function testRealAskReceiptRejectsUnauthorisedContext() public {
        bytes32 wrongContext = expectedContext ^ bytes32(uint256(1));
        FactoidalAskGate wrong = new FactoidalAskGate(expectedImage, expectedPolicy, wrongContext);
        vm.expectRevert(
            abi.encodeWithSelector(FactoidalAskGate.ContextMismatch.selector, expectedContext, wrongContext)
        );
        wrong.verifyTrue(seal, journal);
    }

    function testRealAskReceiptRejectsFalse() public {
        bytes memory changed = journal;
        changed[127] = 0;
        vm.expectRevert(FactoidalAskGate.NotSatisfied.selector);
        gate.verifyTrue(seal, changed);
    }

    function testRealAskReceiptRejectsTamperedSeal() public {
        bytes memory changed = seal;
        changed[4] ^= bytes1(uint8(1));
        vm.expectRevert(VerificationFailed.selector);
        gate.verifyTrue(changed, journal);
    }
}
