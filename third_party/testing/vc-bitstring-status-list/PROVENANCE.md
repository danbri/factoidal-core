# Vendored: w3c/vc-bitstring-status-list-test-suite

- **Upstream:** https://github.com/w3c/vc-bitstring-status-list-test-suite
- **Commit:** `960ab9a3ad275bb5e56dd3f300939f83cba759b7` (2026-09-02T11:40:07-04:00)
- **Retrieved:** 2026-10-28, `git clone --depth 1`; `.git` removed.
- **Licence:** the repository has no LICENSE file. Its source files carry
  `SPDX-License-Identifier: LicenseRef-w3c-3-clause-bsd-license-2008 OR
  LicenseRef-w3c-test-suite-license-2023` (for example `tests/mock.data.js`),
  the W3C test suite licences.

Suite for Bitstring Status List v1.0 (W3C Recommendation 2025-05-15). Run
against `bin/vc-api-shim/server.mjs` by `tests/vc-bitstring-status-list/run.sh`.

- `node_modules/` is not committed. Install with
  `(cd third_party/testing/vc-bitstring-status-list && npm install)` (network
  once).
- The suite dereferences `statusListCredential` URLs over HTTPS only
  (`tests/documentLoader.js` registers an `https` handler, with certificate
  checks off). The runner therefore starts the shim with a TLS listener and a
  self-signed certificate made by `openssl` for that run.
