// SPDX-License-Identifier: Apache-2.0
pragma solidity ^0.8.26;

import {Test} from "forge-std/Test.sol";
import {TestReceipt} from "risc0-ethereum/test/TestReceiptV3_1.sol";
import {VerificationFailed} from "risc0-ethereum/src/IRiscZeroVerifier.sol";
import {
    RiscZeroGroth16Verifier,
    SelectorMismatch
} from "risc0-ethereum/src/groth16/RiscZeroGroth16Verifier.sol";
import {FactoidalAskGate} from "../src/FactoidalAskGate.sol";

/// @dev These tests use the official real Groth16 fixture to check the verifier,
///      and malformed ASK statements to check rejection. They do not assert that
///      the upstream fixture is an ASK proof. The separate proof profile requires one.
contract FactoidalAskGateTest is Test {
    bytes32 internal constant GRAPH = hex"3714978ba3a9a0943c0daba1ccec95eaa7177b25f58768af7b7dac48807f7a92";
    bytes32 internal constant POLICY = hex"b6eda070896dbba7e5dc4c703a7a2a93ed7c9e1af6bd52368e70fbf05de48cf5";
    bytes32 internal constant CONTEXT = hex"7fbf63bf0092351a1381c010568ebbaf94b7ccb71f7a33b33584e194ac7e4bb2";
    FactoidalAskGate internal gate;
    RiscZeroGroth16Verifier internal verifier;

    function setUp() public {
        gate = new FactoidalAskGate(TestReceipt.IMAGE_ID, POLICY, CONTEXT);
        verifier = gate.verifier();
    }

    function journal(uint256 answer) internal pure returns (bytes memory) {
        return abi.encode(GRAPH, POLICY, CONTEXT, answer);
    }

    function testOfficialRealReceiptVerifiesUnderPatchedSelector() public view {
        assertEq(gate.verifier().SELECTOR(), bytes4(hex"e71e6620"));
        gate.verifier().verify(TestReceipt.SEAL, TestReceipt.IMAGE_ID, sha256(TestReceipt.JOURNAL));
    }

    function testOfficialReceiptRejectsChangedImage() public {
        bytes32 journalDigest = sha256(TestReceipt.JOURNAL);
        vm.expectRevert(VerificationFailed.selector);
        verifier.verify(TestReceipt.SEAL, TestReceipt.IMAGE_ID ^ bytes32(uint256(1)), journalDigest);
    }

    function testOfficialReceiptRejectsChangedJournal() public {
        bytes memory changed = TestReceipt.JOURNAL;
        changed[0] ^= bytes1(uint8(1));
        bytes32 journalDigest = sha256(changed);
        vm.expectRevert(VerificationFailed.selector);
        verifier.verify(TestReceipt.SEAL, TestReceipt.IMAGE_ID, journalDigest);
    }

    function rejectSelector(bytes4 selector) internal {
        bytes memory changed = TestReceipt.SEAL;
        for (uint256 i; i < 4; ++i) {
            changed[i] = selector[i];
        }
        bytes32 journalDigest = sha256(TestReceipt.JOURNAL);
        vm.expectRevert(abi.encodeWithSelector(SelectorMismatch.selector, selector, bytes4(hex"e71e6620")));
        verifier.verify(changed, TestReceipt.IMAGE_ID, journalDigest);
    }

    function testRejectsDevelopmentSelector() public {
        rejectSelector(hex"ffffffff");
    }

    function testRejectsSupersededV31Selector() public {
        rejectSelector(hex"8b38038c");
    }

    function testRejectsV30Selector() public {
        rejectSelector(hex"73c457ba");
    }

    function testOfficialReceiptIsNotAnAskProof() public {
        vm.expectRevert(
            abi.encodeWithSelector(FactoidalAskGate.JournalLength.selector, TestReceipt.JOURNAL.length)
        );
        gate.verifyTrue(TestReceipt.SEAL, TestReceipt.JOURNAL);
    }

    function testWellFormedAskJournalRequiresItsOwnProof() public {
        vm.expectRevert(VerificationFailed.selector);
        gate.verifyTrue(TestReceipt.SEAL, journal(1));
    }

    function testRejectsShortJournal() public {
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.JournalLength.selector, 127));
        gate.verifyTrue(TestReceipt.SEAL, new bytes(127));
    }

    function testRejectsTrailingJournalBytes() public {
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.JournalLength.selector, 129));
        gate.verifyTrue(TestReceipt.SEAL, bytes.concat(journal(1), hex"00"));
    }

    function testRejectsFalse() public {
        vm.expectRevert(FactoidalAskGate.NotSatisfied.selector);
        gate.verifyTrue(TestReceipt.SEAL, journal(0));
    }

    function testRejectsBooleanTwo() public {
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.NonCanonicalBoolean.selector, 2));
        gate.verifyTrue(TestReceipt.SEAL, journal(2));
    }

    function testRejectsNonzeroBooleanPadding() public {
        uint256 malformed = uint256(1) << 255 | 1;
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.NonCanonicalBoolean.selector, malformed));
        gate.verifyTrue(TestReceipt.SEAL, journal(malformed));
    }

    function testRejectsUnauthorisedPolicy() public {
        bytes32 wrong = POLICY ^ bytes32(uint256(1));
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.PolicyMismatch.selector, wrong, POLICY));
        gate.verifyTrue(TestReceipt.SEAL, abi.encode(GRAPH, wrong, CONTEXT, true));
    }

    function testRejectsUnauthorisedContext() public {
        bytes32 wrong = CONTEXT ^ bytes32(uint256(1));
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.ContextMismatch.selector, wrong, CONTEXT));
        gate.verifyTrue(TestReceipt.SEAL, abi.encode(GRAPH, POLICY, wrong, true));
    }

    function testRejectsMissingSeal() public {
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.SealLength.selector, 0));
        gate.verifyTrue(hex"", journal(1));
    }

    function testRejectsTrailingSealBytes() public {
        vm.expectRevert(abi.encodeWithSelector(FactoidalAskGate.SealLength.selector, 261));
        gate.verifyTrue(bytes.concat(TestReceipt.SEAL, hex"00"), journal(1));
    }

    function testRejectsZeroConfiguration() public {
        vm.expectRevert(FactoidalAskGate.InvalidConfiguration.selector);
        new FactoidalAskGate(bytes32(0), POLICY, CONTEXT);
    }
}
