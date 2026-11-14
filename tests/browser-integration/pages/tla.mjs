// A module with top-level await: it reports to the classic script's check (awaitDone).
const value = await Promise.resolve('awaited');
globalThis.awaitDone(value);
