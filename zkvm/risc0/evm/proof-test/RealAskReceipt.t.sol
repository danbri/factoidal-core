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
        string memory expected = vm.readFile("fixtures/expected-statement.json");
        expectedImage = vm.parseJsonBytes32(expected, ".imageId");
        bytes memory expectedJournal = vm.parseJsonBytes(expected, ".journal");
        require(expectedJournal.length == 128, "expected journal must have 128 bytes");
        uint256 answer;
        (expectedGraph, expectedPolicy, expectedContext, answer) =
            abi.decode(expectedJournal, (bytes32, bytes32, bytes32, uint256));
        require(answer == 1, "expected statement must authorise true");
        gate = new FactoidalAskGate(expectedImage, expectedPolicy, expectedContext);

        string memory proof = vm.readFile("fixtures/ask-proof.json");
        require(vm.parseJsonBytes32(proof, ".imageId") == expectedImage, "proof image differs");
        seal = vm.parseJsonBytes(proof, ".seal");
        journal = vm.parseJsonBytes(proof, ".journal");
        assertEq(journal, expectedJournal, "proof journal differs from authorised statement");
    }

    function testRealAskReceiptVerifies() public view {
        assertEq(gate.verifyTrue(seal, journal), expectedGraph);
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
        vm.expectRevert();
        gate.verifyTrue(changed, journal);
    }
}
