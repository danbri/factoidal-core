# Web renderer script engine, 3 November 2026

Added a real QuickJS-NG 0.18.0 WASI reactor in a dedicated worker. The
checksum-pinned upstream binary is fetched into ignored `.build/` storage.
No QuickJS native build or npm dependency is required.

Lean owns script discovery, element handles and checked DOM mutation.
`WebRenderScript.lean` projects the DOM and applies typed `setTextContent`
and `setAttribute` commands through the existing arena implementation.
The browser keeps the original HTML source and sends a bounded command
history to Lean for font requests and rendering.

The design, current binding limits, engine choice, VerifiedJS assessment,
shared-memory tradeoffs and reproduction commands are in
[the architecture decision](designissues/2026-11-03-script-engine-architecture.md).

Validation: 10 real Node worker tests pass, including cooperative interruption,
forced worker termination, restart, memory exhaustion and message validation.
Click tests cover explicit cancellation, event-local flags, updated anchor
commands, and the distinct return-value rules for listener/property handlers.
The Lean boundary and its guards elaborate. Browser integration is validated
with the complete MVP build; this worknote alone does not claim that result.
