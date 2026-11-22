/-
Native/guest edge for the checked ASK computation, issue #745.
The only hash implementation here is the existing HACL* SHA-256 FFI.
Its agreement with the pure specification is a measured trust boundary.
This export produces a journal, not a proof or a verified receipt.
-/
import L4Factoidal.Attestation.Ask
import L4Factoidal.Crypto.SHA2Native

namespace Harness.AskAttestation

open L4Factoidal

/-- Managed Lean C ABI: five owned ByteArray objects followed by uint8_t.
The result is a managed Lean pair (UInt8, ByteArray). Its first object
field is a boxed UInt8; its second object field is the journal byte array.

Regime 0 = simple; 1 = full RDFS then SPARQL-RL; other codes refuse.
Status 0 = successful false; 1 = successful true; 2 = invalid input/policy;
3 = exhausted; 4 = resource limit; 5 = hash refusal.
Only statuses 0 and 1 carry a 128-byte ABI journal. Every failure carries
an empty byte array, so false and a failed computation remain distinct.
Initialise the module before calling this export. For a Lake package build
the generated symbol is initialize_l4factoidal_Harness_AskAttestationExports
(uint8_t); direct Lean builds omit the package prefix. Inspect the emitted
C declaration when linking a different build mode.

The caller must bound and frame all five byte arrays before allocating
them. The fixed profile has input <= 65536, salt = 32, query + rules <=
16384 and context <= 4096 bytes. Lean validates them again. -/
@[export l4_ask_attest_native]
def attestNative (originalBytes salt query rules context : ByteArray)
    (regime : UInt8) : UInt8 × ByteArray :=
  Attestation.abiResult (Attestation.attestRequest Crypto.sha256Hacl
    originalBytes salt query rules context regime)

end Harness.AskAttestation
