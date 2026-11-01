# Browser-safe import of the LWS client host

The LWS client previously imported the Node engine loader when the module was
first evaluated, even when callers supplied an already loaded engine. This
pulled Node-only dependencies into the compositor's browser module graph.
`createLwsClient` and `createDidKey` now import that loader only when the caller
omits `options.engine`. Injected engines use the same existing protocol
operations. No protocol, authorization or conflict-resolution rule changes.

Two standalone npm regressions check injected-engine operations and evaluate
the actual client module in a restricted VM context without Node imports or
Buffer. The VM admits only the client and its error module, then executes a
request through the injected engine and fetch implementation. A Node loader
import fails the test. These controls are selected by the existing npm test
file glob and do not need engine binaries or a listening socket.

```sh
node --test npm/factoidal/test/lws-browser-import.test.mjs
```

Both pass. They establish import and host-boundary behavior, not browser CORS,
server authorization or actual Lean operation correctness. The separate pod
suite currently passes nine tests but cannot complete its real socket test in
this environment (`listen EPERM` on localhost). That failure is retained, not
skipped or represented as a successful network roundtrip. The full compositor
storage UI remains separate work; this source change is not an npm release.
