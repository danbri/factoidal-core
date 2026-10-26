# Research note: confidential computing and tenancy for an LWS server (2026-10-21)

Owner decision, 2026-10-21: "3. Research note for now." No work is planned.
This note records the question and the options as known on that date. Nothing
here was tested in this repository; the claims about products come from their
public documentation as remembered by the author, and must be checked against
current vendor documentation before any work starts.

## The question

Owner, 2026-10-21: "Does LWS spec say anything about data being encrypted at
rest? Can we have encrypted while in use in memory somehow for our server? Or
at least prove sole tenancy (and not in a vm) in some fancy hosting
environments?"

## What the LWS drafts say

Nothing about encryption at rest or in use (w3c/lws-protocol 9a08ff65). The
only related sentence, in `lws10-core/Security-Considerations.html`, is about
tokens: "Any time an unencrypted token is stored in a browser's localStorage,
in URLs, or in logs, that token is more susceptible to an exfiltration
attack." Encryption at rest of our own storage file is tracked separately:
https://github.com/danbri/factoidal/issues/921.

## Encryption in use

Hardware that encrypts the memory of a workload so that the host operating
system and the hypervisor cannot read it, and that can sign a report of what
code runs (remote attestation):

| technology | unit of isolation | attestation |
|---|---|---|
| AMD SEV-SNP | a virtual machine (confidential VM) | report signed by a key specific to the processor |
| Intel TDX | a virtual machine (trust domain) | quote signed through Intel's attestation service |
| AWS Nitro Enclaves | an isolated part of an EC2 instance | document signed by the Nitro hypervisor |
| Intel SGX | an enclave inside a process | quote |
| Arm CCA | a realm (virtual machine) | realm token |

What attestation could give this project: a chain from a Lean theorem to the
running server. Theorem, source commit in `danbri/factoidal-core`, release of
`danbri/factoidal-builds` with the sha256 of each artifact in
`build-info.json`, and the measurement in an attestation report. A client could
then check, before it sends data, that the storage server runs a given
release. This needs a reproducible build of the whole image that is measured
(the wasm, the Node runtime and the operating system), not only of the wasm.

## "Not in a VM" and sole tenancy

- SEV-SNP, TDX and Arm CCA are themselves virtual machines. Their attestation
  proves a confidential guest on genuine hardware with given code and policy.
  It does not prove the absence of a hypervisor; the hypervisor is present but
  cannot read the guest's memory.
- No attestation that we know of proves sole tenancy of a physical machine.
  Sole tenancy comes from a dedicated host or a bare-metal instance and the
  provider's contract.
- On bare metal, a TPM quote over the measured boot (platform configuration
  registers) shows which firmware, boot loader and kernel started. It can show
  that no hypervisor was in the boot chain. This is the nearest technical
  evidence for "not in a VM". It still trusts the TPM, the firmware and the
  provider's hardware.

## Limits to state in any later work

- Attestation proves what code started, not that the code is correct. The
  correctness argument is the Lean proofs and the test suites; attestation only
  connects them to the running instance.
- Side channels are outside the guarantee of every technology above.
- Keys: memory encryption does not solve key management for data at rest or
  for TLS.

## If work starts later

1. A reproducible container or VM image of `factoidal lws-serve`, with its
   measurement published next to the release.
2. A trial on one provider that offers confidential VMs, with an attestation
   report served at a well-known path, and a client check.
3. An issue per step, with the owner's choice of provider.
