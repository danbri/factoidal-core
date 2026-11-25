# Cookie navigation host contract

Work: https://github.com/danbri/factoidal-core/pull/596.
Overview: https://github.com/danbri/factoidal-core/issues/598.

The failed Linux gate reported one unknown host operation:
`native_html_engine.ts: cookies`. Reproduced on the cookie branch after merging
current main: the existing host-contract source tests gave two passes and one
failure. No cookie policy failure was reported by that test.

`WebDocument` handles `request`, `response` and `keep` by reading the jar and
other fields from the request and returning the calculated cookie header or jar.
It changes no held engine state. The host keeps the returned jar and performs
network and disk I/O. The operation is therefore a query with no capability
needed for the calculation itself, as with the download decision operation.

Register `cookies` in `HostContract.ops` and update the count from 70 to 71.
`HostContract.cookies_contract` states only the table classification and empty
capability list. Its axiom report is printed by the build. It does not prove
host persistence or networking correct. The cookie branch retains its existing
`sentNav_safe`, `persistent_no_session` and `ofWire_wellformed` theorems.

The existing source-contract tests run with `deno test --no-check --allow-read
labs/demos/foafnaut/host_contract_source_test.ts`: the local checkout lacks the
Node type package, so TypeScript checking is deferred to the Linux gate. No
timing change is claimed: this repair changes the contract inventory, not the
cookie handler or the navigation algorithm. Full engine validation remains the
Linux gate on the pushed branch.
