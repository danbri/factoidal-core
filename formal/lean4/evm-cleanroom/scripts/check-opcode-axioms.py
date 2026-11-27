#!/usr/bin/env python3
"""Audit the axioms of the instruction-set theorems (issues #649, #744).

Runs the pinned Lean toolchain on each listed source and requires, for every
listed theorem, exactly one actual `#print axioms` report whose set equals the
recorded set, drawn only from propext, Classical.choice and Quot.sound. A
`sorryAx` or any user axiom fails the gate. `--selftest` checks the parser
against corrupted transcripts (negative controls) without running Lean.

This is an axiom audit of the selected theorems, not a proof of refinement to
the Ethereum execution specification.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("active_axioms", ROOT / "scripts/check-axiom-output.py")
ACTIVE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ACTIVE)
require = ACTIVE.require

P, C, Q = "propext", "Classical.choice", "Quot.sound"
# file -> {theorem: recorded axiom set}
INVENTORY = {
    "EVMCleanroom/Core.lean": {
        "EVMCleanroom.step_tload": [P, Q],
        "EVMCleanroom.step_tstore": [P, Q],
        "EVMCleanroom.step_tstore_static": [P, Q],
        "EVMCleanroom.step_tstore_outOfGas": [P, Q],
        "EVMCleanroom.step_cancun_opcodes_unknown_fork": [P, Q],
        "EVMCleanroom.commit_static_transient": [P, Q],
        "EVMCleanroom.step_tstore_transient": [P, Q],
        "EVMCleanroom.step_mcopy": [P, Q],
        "EVMCleanroom.mcopy_reads_source": [P, Q],
        "EVMCleanroom.step_mcopy_outOfGas": [P, Q],
        "EVMCleanroom.mcopyCost_zero": [P, C, Q],
        "EVMCleanroom.step_blockHash_window": [P, Q],
        "EVMCleanroom.step_blockHash_outside": [P, Q],
        "EVMCleanroom.step_blockHash_missing": [P, Q],
    },
    "EVMCleanroom/AccountOpcode.lean": {
        "EVMCleanroom.AccountOpcode.accountStep_balance": [P, C, Q],
        "EVMCleanroom.AccountOpcode.accountStep_extCodeSize": [P, C, Q],
        "EVMCleanroom.AccountOpcode.accountStep_extCodeHash_empty": [P, Q],
        "EVMCleanroom.AccountOpcode.accountStep_extCodeHash_disabled": [P, Q],
        "EVMCleanroom.AccountOpcode.accountStep_extCodeCopy": [P, C, Q],
        "EVMCleanroom.AccountOpcode.accountStep_extCodeCopy_outOfGas": [P, C, Q],
        "EVMCleanroom.AccountOpcode.accountStep_uncovered": [P, Q],
        "EVMCleanroom.AccountOpcode.accountStep_preShanghai": [P, Q],
        "EVMCleanroom.AccountOpcode.accountStep_world": [P, Q],
    },
    "EVMCleanroom/CallOpcode.lean": {
        "EVMCleanroom.CallOpcode.finishCall_transient_projection": [],
        "EVMCleanroom.CallOpcode.executeAtDepth_account": [P, C, Q],
        "EVMCleanroom.CallOpcode.executeAtDepth_account_error": [P, C, Q],
        "EVMCleanroom.CallOpcode.resumeChild_failure_transient": [P],
        "EVMCleanroom.CallOpcode.beginCall_checkpoint_transient": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_preShanghai": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_underflow": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_outOfGas": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_oversize": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_static": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_uncovered_creator": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_admitted": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_soft_failure": [P, C, Q],
        "EVMCleanroom.CallOpcode.beginCreate_no_keccak": [P, Q],
        "EVMCleanroom.CallOpcode.enterCreate_uncovered": [P, Q],
        "EVMCleanroom.CallOpcode.enterCreate_collision": [P, Q],
        "EVMCleanroom.CallOpcode.enterCreate_entered": [P, Q],
        "EVMCleanroom.CallOpcode.beginCreate_entered": [P, C, Q],
        "EVMCleanroom.CallOpcode.resumeCreate_revert": [P],
        "EVMCleanroom.CallOpcode.resumeCreate_exception": [P],
        "EVMCleanroom.CallOpcode.resumeCreate_deposit_failure": [P],
        "EVMCleanroom.CallOpcode.resumeCreate_success": [P, Q],
        "EVMCleanroom.CallOpcode.createContinuation_parent": [],
        "EVMCleanroom.CallOpcode.executeAtDepth_create_error": [P, C, Q],
        "EVMCleanroom.CallOpcode.executeAtDepth_create_failed": [P, C, Q],
        "EVMCleanroom.CallOpcode.executeAtDepth_selfDestruct": [P, C, Q],
        "EVMCleanroom.CallOpcode.executeAtDepth_selfDestruct_error": [P, C, Q],
        "EVMCleanroom.CallOpcode.executeLoop_selfDestruct_child": [P, C, Q],
        "EVMCleanroom.CallOpcode.resumeChild_failure_registration": [P],
        "EVMCleanroom.CallOpcode.settle_failure_registration": [],
    },
    "EVMCleanroom/Create.lean": {
        "EVMCleanroom.Create.charge_create": [P],
        "EVMCleanroom.Create.charge_create2": [P],
        "EVMCleanroom.Create.childGas_reserve": [P, C, Q],
        "EVMCleanroom.Create.fixedBytes_length": [P],
        "EVMCleanroom.Create.byteLength_le": [P, Q],
        "EVMCleanroom.Create.rlpScalar_length": [P, Q],
        "EVMCleanroom.Create.rlpSenderNonce_shape": [P, Q],
        "EVMCleanroom.Create.create2Preimage_shape": [P],
        "EVMCleanroom.Create.address_bound": [P, Q],
        "EVMCleanroom.Create.materialize_bytes": [P, C, Q],
        "EVMCleanroom.Create.deposit_oversize": [P],
        "EVMCleanroom.Create.deposit_invalid_prefix": [P, C, Q],
        "EVMCleanroom.Create.deposit_outOfGas": [P],
        "EVMCleanroom.Create.deposit_success": [P, C, Q],
        "EVMCleanroom.Create.deposit_empty": [P, Q],
        "EVMCleanroom.Create.bumpNonce_accounts": [P, Q],
        "EVMCleanroom.Create.bumpNonce_journal": [],
        "EVMCleanroom.Create.prepare_new": [P, Q],
        "EVMCleanroom.Create.setCode_effect": [P, Q],
        "EVMCleanroom.Create.collides_iff": [P, Q],
    },
    "EVMCleanroom/SelfDestruct.lean": {
        "EVMCleanroom.SelfDestruct.gasCost_values": [P, Q],
        "EVMCleanroom.SelfDestruct.selfDestructStep_gas": [P],
        "EVMCleanroom.SelfDestruct.selfDestructStep_outOfGas": [P, Q],
        "EVMCleanroom.SelfDestruct.selfDestructStep_static": [P, Q],
        "EVMCleanroom.SelfDestruct.selfDestructStep_fork": [P],
        "EVMCleanroom.SelfDestruct.selfDestructStep_uncovered": [P],
        "EVMCleanroom.SelfDestruct.selfDestructStep_halts": [P],
        "EVMCleanroom.SelfDestruct.selfDestructStep_warms": [P, Q],
        "EVMCleanroom.SelfDestruct.selfDestructStep_notCreated": [P, Q],
        "EVMCleanroom.SelfDestruct.selfDestructStep_created": [P, Q],
        "EVMCleanroom.SelfDestruct.selfDestructStep_registeredCreated": [P, Q],
        "EVMCleanroom.SelfDestruct.destroyRegistered_accounts": [P, Q],
        "EVMCleanroom.SelfDestruct.destroyRegistered_keeps_old": [P, Q],
        "EVMCleanroom.SelfDestruct.destroyRegistered_fields": [],
        "EVMCleanroom.SelfDestruct.destroyRegistered_none": [P],
    },
    "EVMCleanroom/CallTransaction.lean": {
        "EVMCleanroom.CallTransaction.destroyAfter_executed": [],
    },
    "EVMCleanroom/CallTransactionProofs.lean": {
        "EVMCleanroom.CallTransaction.settleFrame_success_destroys": [P, Q],
    },
    "EVMCleanroom/AccountTransientProofs.lean": {
        "EVMCleanroom.AccountTransient.witnessWorld_transient_empty": [],
        "EVMCleanroom.AccountTransient.debitSender_transient": [],
        "EVMCleanroom.AccountTransient.pay_transient": [],
        "EVMCleanroom.AccountTransient.entryFrame_transient_empty": [],
        "EVMCleanroom.AccountTransient.frameInput_transient": [],
        "EVMCleanroom.AccountTransient.commitFrame_transient": [],
    },
}
# Sources that print only listed theorems.
EXACT_SOURCES = {"EVMCleanroom/AccountOpcode.lean", "EVMCleanroom/AccountTransientProofs.lean",
                 "EVMCleanroom/Create.lean", "EVMCleanroom/SelfDestruct.lean"}


def expected_claims(source):
    return [{"name": name, "axioms_printed": axioms} for name, axioms in INVENTORY[source].items()]


def check(expected, transcript, exact=False):
    printed = ACTIVE.extract_printed(transcript)
    ACTIVE.verify_printed(expected, printed)
    if exact:
        require(set(printed) == {x["name"] for x in expected}, "unexpected theorem output in dedicated source")
    return {x["name"]: sorted(printed[x["name"]][0]) for x in expected}


def selftest():
    expected = [
        {"name": "EVMCleanroom.step_tload", "axioms_printed": [P, Q]},
        {"name": "EVMCleanroom.AccountTransient.frameInput_transient", "axioms_printed": []},
    ]
    good = ("info: Core.lean:1:0: 'EVMCleanroom.step_tload' depends on axioms: [propext,\n Quot.sound]\n"
            "'EVMCleanroom.AccountTransient.frameInput_transient' does not depend on any axioms\n")
    require(len(check(expected, good, True)) == 2, "positive control failed")
    corrupt = {
        "missing-theorem": good.split("\n'", 1)[0],
        "duplicate-report": good + good,
        "sorryAx": good.replace("Quot.sound]", "sorryAx,\n Quot.sound]"),
        "user-axiom": good.replace("Quot.sound]", "EVMCleanroom.unproved, Quot.sound]"),
        "dropped-axiom": good.replace("propext,\n ", ""),
        "extra-theorem": good + "'EVMCleanroom.AccountOpcode.extra' does not depend on any axioms\n",
    }
    rejected = []
    for label, transcript in corrupt.items():
        try:
            check(expected, transcript, True)
        except ValueError:
            rejected.append(label)
    require(sorted(rejected) == sorted(corrupt), "a corrupted transcript was accepted")
    return {"status": "negative-controls-pass", "rejected": len(rejected)}


def run():
    results, total = {}, 0
    for source in INVENTORY:
        out = subprocess.run(["lake", "env", "lean", source], cwd=ROOT, capture_output=True, text=True)
        require(out.returncode == 0, "Lean failed on " + source + ": " + out.stdout[-2000:] + out.stderr[-2000:])
        results[source] = check(expected_claims(source), out.stdout + out.stderr, source in EXACT_SOURCES)
        total += len(results[source])
    return {"status": "printed-axioms-match", "theorems": total, "sources": len(results), "axioms": results}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--selftest", action="store_true")
    args = parser.parse_args()
    try:
        print(json.dumps(selftest() if args.selftest else run()))
    except ValueError as error:
        print(json.dumps({"status": "fail", "reason": str(error)}))
        sys.exit(1)
