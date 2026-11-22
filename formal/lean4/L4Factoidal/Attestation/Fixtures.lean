/- Public reproducible fixture for issue #745. The fixed salt is only for
this fixture. Deployments supply 32 fresh CSPRNG bytes for each witness.
The expected journal was independently encoded and hashed with Python's
standard hashlib SHA-256. The test modules compare Lean and HACL* paths. -/
import L4Factoidal.Attestation.Ask

namespace L4Factoidal.Attestation.Fixtures

def input : ByteArray :=
  "<urn:a> <urn:p> <urn:b> .\n<urn:b> <urn:p> <urn:c> .\n".toUTF8
def salt : ByteArray := ByteArray.mk (Array.replicate 32 7)
def query : ByteArray := "ASK { <urn:a> <urn:p> <urn:b> }".toUTF8
def rules : ByteArray := ByteArray.empty
def context : ByteArray := "beneficiary=public-fixture;action=check;nonce=1".toUTF8
def journalHex : String :=
  "3714978ba3a9a0943c0daba1ccec95eaa7177b25f58768af7b7dac48807f7a92" ++
  "b6eda070896dbba7e5dc4c703a7a2a93ed7c9e1af6bd52368e70fbf05de48cf5" ++
  "7fbf63bf0092351a1381c010568ebbaf94b7ccb71f7a33b33584e194ac7e4bb2" ++
  "0000000000000000000000000000000000000000000000000000000000000001"

end L4Factoidal.Attestation.Fixtures
