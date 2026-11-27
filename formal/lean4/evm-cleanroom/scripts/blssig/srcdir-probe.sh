#!/bin/bash
# Can another Lake package take the BLS signature kit by source, without the EVM? A scratch
# package under /tmp (never in the tree) whose lakefile holds exactly the committed stanza
# `scripts/blssig/srcdir-stanza.toml` (srcDir = "../evm-cleanroom", reached through a symbolic
# link to this package) and whose one module imports `EVMCleanroom.Precompiles.BLSSignature`
# and verifies a published signature. Run from the package directory.
set -euo pipefail
package=$PWD
# The committed roots are the import closure, and the closure stays inside Precompiles/.
python3 scripts/blssig/closure.py . --toml | diff -u scripts/blssig/srcdir-stanza.toml - \
  || { echo "FAILURES blssig srcDir: srcdir-stanza.toml is not the import closure of BLSSignature"; exit 1; }
if grep -l -E '^import +(Lean|Std|Mathlib|EVMCleanroom\.(Keccak|Core|CallOpcode))' \
    $(python3 scripts/blssig/closure.py . | sed -e 's|\.|/|g' -e 's|$|.lean|'); then
  echo "FAILURES blssig srcDir: a module of the closure imports Lean, Std, Mathlib, Keccak or the EVM"; exit 1
fi
probe=/tmp/blssig-srcdir-probe
rm -rf "$probe" && mkdir -p "$probe/consumer"
ln -s "$package" "$probe/evm-cleanroom"
cp lean-toolchain "$probe/consumer/"
{
  printf 'name = "bls_srcdir_probe"\nversion = "0.1.0"\ndefaultTargets = ["bls-probe"]\n\n'
  cat scripts/blssig/srcdir-stanza.toml
  printf '\n[[lean_exe]]\nname = "bls-probe"\nroot = "ProbeMain"\n'
} > "$probe/consumer/lakefile.toml"
cat > "$probe/consumer/ProbeMain.lean" <<'LEAN'
import EVMCleanroom.Precompiles.BLSSignature

open EVMCleanroom.Precompiles

/-- Consensus-specification case `verify_valid_case_195246ee3bd3b6ec`. -/
def pk : ByteArray :=
  hex "b53d21a4cfd562c469cc81514d4ce5a6b577d8403d32a394dc265dd190b47fa9f829fdd7963afdf972e5e77854051f6f"
def msg : ByteArray := hex "abababababababababababababababababababababababababababababababab"
def sig : ByteArray :=
  hex ("ae82747ddeefe4fd64cf9cedb9b04ae3e8a43420cd255e3c7cd06a8d88b7c7f8638543719981c5d16fa3527c468c25f0" ++
    "026704a6951bde891360c7e8d12ddee0559004ccdbe6046b55bae1b257ee97f7cdb955773d7cf29adf3ccbb9975e4eb9")

def main : IO UInt32 := do
  let good := BLSSignature.verify pk msg sig
  let bad := BLSSignature.verify pk (msg.push 0) sig
  let decoded :=
    match BLSSignature.decodePublicKey pk, BLSSignature.decodeSignature sig with
    | some key, some signature => BLSSignature.verifyDecoded key msg signature
    | _, _ => false
  IO.println s!"probe: verify {good}, wrong message {bad}, verifyDecoded {decoded}"
  return if good && !bad && decoded then 0 else 1
LEAN
cd "$probe/consumer"
start=$SECONDS
lake build bls-probe 2>&1 | grep -v "depends on axioms\|^info: \|^ *Classical.choice\|^ *Quot.sound\|^ *propext" | tail -15 || true
[ -x .lake/build/bin/bls-probe ] || { echo "FAILURES blssig srcDir: the probe package did not build"; exit 1; }
echo "TIMING blssig srcDir probe: clean build of the $(grep -c '^  "' "$package/scripts/blssig/srcdir-stanza.toml") root modules and the probe in $(( SECONDS - start )) s"
.lake/build/bin/bls-probe || { echo "FAILURES blssig srcDir: the probe gave a wrong verdict"; exit 1; }
# Nothing of the EVM was compiled for it.
built=$(find .lake/build/lib -name '*.olean' | wc -l)
foreign=$(find .lake/build/lib -name '*.olean' | grep -c -v -e '/EVMCleanroom/Precompiles/' -e 'ProbeMain' || true)
echo "RESULT blssig srcDir: a package with the committed stanza builds and verifies ($built compiled modules, $foreign outside EVMCleanroom/Precompiles)"
[ "$foreign" = 0 ] || { echo "FAILURES blssig srcDir: modules outside Precompiles were compiled"; exit 1; }
cd "$package"
rm -rf "$probe"
