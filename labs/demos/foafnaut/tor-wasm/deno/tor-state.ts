// Arti (Tor) state kept in a local, sealed LWS storage (owner, 2026-11-25: "could this be LWS
// pods but local not networked?"). Record: docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md,
// sections 14 and 15.
//
// EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
// WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.
//
// Rules held here:
// - The storage is sealed at rest or it is not used: `lws-serve` must print "encryption at rest
//   is ON" (ChaCha20-Poly1305, HACL*). The key comes from FOAFNAUT_TOR_STATE_KEY (make one with
//   `factoidal lws-keygen`); it is never written to disk by this file.
// - Local only: the server listens on 127.0.0.1, authorization is on, its owner is a did:key kept
//   in DIR/agent.json (mode 0600), and this client fetches nothing but that origin. The state is
//   never copied to a remote pod.
// - Only the host process touches the storage; the Tor worker never gets access to it.
type Log = (line: Record<string, unknown>) => void;

export type TorStateStore = {
  origin: string;
  keyId: string;
  load(): Promise<string | undefined>;
  save(json: string): Promise<void>;
  close(): Promise<void>;
};

const STATE_PATH = "tor/state.json";
const exists = async (p: string) => { try { await Deno.stat(p); return true; } catch { return false; } };

/** The @factoidal/core package: FACTOIDAL_CORE_DIR, or this checkout's npm/factoidal. */
function corePackage(): string {
  const given = Deno.env.get("FACTOIDAL_CORE_DIR");
  if (given) return given.replace(/\/$/, "");
  return new URL("../../../../../npm/factoidal", import.meta.url).pathname;
}

/** Open the sealed store in DIR, or return the reason it cannot be used (the caller then keeps
 *  the state in memory and says so). */
export async function openTorState(dir: string, log: Log = () => {}): Promise<TorStateStore | string> {
  const key = Deno.env.get("FOAFNAUT_TOR_STATE_KEY") ?? "";
  if (!/^([0-9a-fA-F]{64}|[A-Za-z0-9_-]{43})$/.test(key)) {
    return "FOAFNAUT_TOR_STATE_KEY is not set to a 32-byte key (factoidal lws-keygen), so Tor state is not saved";
  }
  const pkg = corePackage();
  const { loadEngine } = await import(`file://${pkg}/bin/engine.mjs`);
  const { createLwsClient, createDidKey } = await import(`file://${pkg}/lws/client.mjs`);
  const engine = await loadEngine();
  await Deno.mkdir(dir, { recursive: true, mode: 0o700 });
  const agentFile = `${dir}/agent.json`;
  let agent: { agent: string; selfIssued: unknown };
  if (await exists(agentFile)) agent = JSON.parse(await Deno.readTextFile(agentFile));
  else {
    agent = await createDidKey({ engine });
    await Deno.writeTextFile(agentFile, JSON.stringify(agent), { mode: 0o600, createNew: true });
  }
  await Deno.chmod(agentFile, 0o600);

  const child = new Deno.Command("node", {
    args: [`${pkg}/bin/factoidal.mjs`, "lws-serve", `${dir}/pod`, "--authz", `${dir}/pod-authz`,
      "--owner", agent.agent, "--host", "127.0.0.1", "--port", "0", "--quiet"],
    clearEnv: true,
    env: { PATH: Deno.env.get("PATH") ?? "", HOME: Deno.env.get("HOME") ?? "", FACTOIDAL_LWS_KEY: key },
    stdin: "null", stdout: "piped", stderr: "piped",
  }).spawn();
  const kill = () => { try { child.kill("SIGTERM"); } catch { /* gone */ } };
  let out = "", err = "";
  const errs = (async () => { for await (const c of child.stderr.pipeThrough(new TextDecoderStream())) err += c; })();
  const reader = child.stdout.pipeThrough(new TextDecoderStream()).getReader();
  const deadline = Date.now() + 30000;
  let origin = "";
  while (!origin && Date.now() < deadline) {
    const { value, done } = await reader.read();
    if (done) { await errs; return `lws-serve stopped: ${err.trim().split("\n").slice(-1)[0] ?? ""}`; }
    out += value;
    origin = /^(http:\/\/127\.0\.0\.1:\d+)$/m.exec(out)?.[1] ?? "";
  }
  reader.releaseLock();
  child.stdout.cancel().catch(() => {});
  await new Promise((r) => setTimeout(r, 100));
  const sealed = /encryption at rest is ON: .* under key id ([0-9a-f]+)/.exec(err);
  if (!origin || !sealed) {
    kill();
    return origin ? "the Tor state storage is not sealed at rest; refused" : "lws-serve did not start in 30 s";
  }
  // Fetch only this origin: the state must not go anywhere else.
  const localFetch = (input: string | URL | Request, init?: RequestInit) => {
    const url = typeof input === "string" ? input : input instanceof URL ? input.href : input.url;
    if (!url.startsWith(origin + "/")) return Promise.reject(new Error(`tor state: refused ${new URL(url).origin}`));
    return fetch(input, init);
  };
  const client = await createLwsClient({ engine, selfIssued: agent.selfIssued, fetch: localFetch });
  const base = origin + "/";
  // The LWS client puts the HTTP status in error.detail.status (npm/factoidal/lws/client.mjs).
  const status = (e: unknown) => (e as { detail?: { status?: number } })?.detail?.status ?? 0;
  log({ step: "tor-state", origin, keyId: sealed[1] });
  return {
    origin,
    keyId: sealed[1],
    async load() {
      try {
        const r = await client.read(base + STATE_PATH);
        return typeof r.body === "string" ? r.body : new TextDecoder().decode(r.body);
      } catch (e) {
        if (status(e) === 404) return undefined;
        throw e;
      }
    },
    async save(json: string) {
      try {
        await client.update(base + STATE_PATH, { body: json, mediaType: "application/json" });
        return;
      } catch (e) {
        if (status(e) !== 404) throw e;
      }
      try { await client.head(base + "tor/"); } catch (e) {
        if (status(e) !== 404) throw e;
        await client.create(base, { slug: "tor", container: true });
      }
      await client.create(base + "tor/", { slug: "state.json", body: json, mediaType: "application/json" });
    },
    async close() { kill(); await child.status; await errs; },
  };
}
