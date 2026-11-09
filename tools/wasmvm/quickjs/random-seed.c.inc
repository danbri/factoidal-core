
/* ---- foafnaut: appended by tools/wasmvm/build-quickjs.sh (not part of QuickJS-NG) ----
 * A session's own Math.random seed. The guest's memory is prepared once and copied for
 * every page session; without this every page would repeat the seed the context took
 * when it was made. The engine gives the seed (Hosts.WebApi op 33, mathRandomSeed).
 * Record: docs/designissues/2026-11-09-crypto-boundary-security.md, finding F2. */
void JS_SetRandomSeed(JSContext *ctx, uint64_t seed)
{
    ctx->random_state = seed ? seed : 1;
}
