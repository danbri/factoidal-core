// Shared by the viewer and the screensavers: one stdin reader and the key names of its chunks.
const decoder = new TextDecoder();

/** Reads stdin in one loop, so that a query with a timeout does not lose a key. */
export class Input {
  private queue: Uint8Array[] = [];
  private wake?: () => void;
  private poked = false;
  closed = false;
  constructor() { this.pump(); }
  private async pump() {
    const buffer = new Uint8Array(4096);
    while (true) { // Ends at the end of input.
      const n = await Deno.stdin.read(buffer).catch(() => null);
      if (n === null) { this.closed = true; this.wake?.(); return; }
      this.queue.push(buffer.slice(0, n));
      this.wake?.();
    }
  }
  /** Make a waiting or the next `next` return at once. */
  poke() { this.poked = true; this.wake?.(); }
  /** The next chunk; null on timeout, on poke or at the end of input. */
  async next(timeout?: number): Promise<Uint8Array | null> {
    if (!this.queue.length && !this.poked && !this.closed) {
      let timer: number | undefined;
      await new Promise<void>((resolve) => {
        this.wake = resolve;
        if (timeout !== undefined) timer = setTimeout(resolve, timeout);
      });
      clearTimeout(timer);
      this.wake = undefined;
    }
    this.poked = false;
    return this.queue.shift() ?? null;
  }
}

/** Key names of one input chunk. An unknown sequence gives no key. */
export function keysOf(bytes: Uint8Array): string[] {
  const text = decoder.decode(bytes), keys: string[] = [];
  const names: Record<string, string> = { A: "up", B: "down", C: "right", D: "left", H: "home", F: "end", Z: "backtab", "5~": "pageup", "6~": "pagedown", "1~": "home", "4~": "end" };
  for (let i = 0; i < text.length;) {
    if (text[i] !== "\x1b") { keys.push(text[i]); i++; continue; }
    const match = /^\x1b(?:\[([0-9;?]*[ -/]*[@-~])|O([@-~])|.)?/s.exec(text.slice(i))!;
    const name = names[match[1] ?? match[2] ?? ""];
    if (name) keys.push(name);
    i += match[0].length;
  }
  return keys;
}

