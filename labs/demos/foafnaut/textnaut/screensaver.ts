// textnaut --screensaver [NAME]: colour screensavers for the terminal. Uses no page and no engine.
// Half-block characters give two colour pixels per cell. 24-bit colour when the terminal says so,
// else 256 colours. Every key but n quits; n changes effect. The terminal is restored on exit.

export type RGB = [number, number, number];
type Pixel = (x: number, y: number, t: number, w: number, h: number) => RGB;
type Frame = (t: number, cols: number, rows: number, colour: Colour) => string;
export type Colour = "24bit" | "256";

const clamp = (v: number) => Math.max(0, Math.min(255, Math.round(v)));
const hsv = (h: number, s: number, v: number): RGB => {
  const f = (n: number) => { const k = (n + h * 6) % 6; return clamp(255 * (v - v * s * Math.max(0, Math.min(k, 4 - k, 1)))); };
  return [f(5), f(3), f(1)];
};
const fg = ([r, g, b]: RGB, c: Colour) => c === "24bit" ? `\x1b[38;2;${r};${g};${b}m` : `\x1b[38;5;${cube(r, g, b)}m`;
const bg = ([r, g, b]: RGB, c: Colour) => c === "24bit" ? `\x1b[48;2;${r};${g};${b}m` : `\x1b[48;5;${cube(r, g, b)}m`;
const cube = (r: number, g: number, b: number) => 16 + 36 * Math.round(r / 51) + 6 * Math.round(g / 51) + Math.round(b / 51);

/** A frame from a function of a pixel: each cell is an upper and a lower pixel. */
function pixels(p: Pixel): Frame {
  return (t, cols, rows, c) => {
    const out: string[] = [];
    let lastF = "", lastB = "";
    for (let y = 0; y < rows; y++) {
      out.push(`\x1b[${y + 1};1H`);
      for (let x = 0; x < cols; x++) {
        const f = fg(p(x, y * 2, t, cols, rows * 2), c), b = bg(p(x, y * 2 + 1, t, cols, rows * 2), c);
        if (f !== lastF) { out.push(f); lastF = f; }
        if (b !== lastB) { out.push(b); lastB = b; }
        out.push("▀");
      }
    }
    return out.join("");
  };
}

const plasma: Frame = pixels((x, y, t, w, h) => {
  const u = x / w * 12, v = y / h * 8;
  const n = Math.sin(u + t) + Math.sin(v * 1.3 - t * 0.7) + Math.sin((u + v + t) * 0.7) + Math.sin(Math.hypot(u - 6, v - 4) * 1.6 - t * 1.4);
  return hsv((n / 8 + 0.5 + t * 0.05) % 1, 0.85, 0.95);
});

const tunnel: Frame = pixels((x, y, t, w, h) => {
  const dx = (x - w / 2) / h * 2, dy = (y - h / 2) / h * 2, r = Math.hypot(dx, dy) + 0.001, a = Math.atan2(dy, dx) / Math.PI;
  const check = (Math.floor(1 / r * 3 + t * 3) + Math.floor(a * 6 + t * 0.6)) % 2 === 0;
  return hsv((1 / r * 0.1 + t * 0.08) % 1, 0.8, Math.min(1, r * 1.4) * (check ? 1 : 0.35));
});

/** Fire: heat rises from the bottom row and cools. The state is resized with the terminal. */
function fire(): Frame {
  let w = 0, h = 0, heat = new Float32Array(0);
  const paint = pixels((x, y) => {
    const v = heat[y * w + x] ?? 0;
    return [clamp(v * 3), clamp(v * 3 - 255), clamp(v * 3 - 510)];
  });
  return (t, cols, rows, c) => {
    if (cols !== w || rows * 2 !== h) { w = cols; h = rows * 2; heat = new Float32Array(w * h); }
    for (let x = 0; x < w; x++) heat[(h - 1) * w + x] = Math.random() < 0.6 ? 255 : 90;
    for (let y = 0; y < h - 1; y++) for (let x = 0; x < w; x++) {
      const below = heat[(y + 1) * w + x], l = heat[(y + 1) * w + (x + w - 1) % w], r = heat[(y + 1) * w + (x + 1) % w], far = heat[Math.min(h - 1, y + 2) * w + x];
      heat[y * w + x] = Math.max(0, (below + l + r + far) / 4 - 1.1 - 40 / h);
    }
    return paint(t, cols, rows, c);
  };
}

/** Falling glyphs in rainbow columns. */
function rain(): Frame {
  const glyphs = "ｦｧｨｩｪｱｲｳｴｵｶｷｸｹｺ0123456789FOAFNAUT";
  let drops: number[] = [], speed: number[] = [], last = 0;
  return (t, cols, rows, c) => {
    if (drops.length !== cols) {
      drops = Array.from({ length: cols }, () => Math.random() * rows);
      speed = Array.from({ length: cols }, () => 6 + Math.random() * 22);
    }
    const dt = Math.min(0.2, t - last); last = t;
    const out: string[] = ["\x1b[48;5;16m"];
    for (let x = 0; x < cols; x++) {
      drops[x] += speed[x] * dt;
      if (drops[x] - 22 > rows) { drops[x] = 0; speed[x] = 6 + Math.random() * 22; }
      const head = Math.floor(drops[x]);
      for (let y = 0; y < rows; y++) {
        const d = head - y;
        out.push(`\x1b[${y + 1};${x + 1}H`);
        if (d < 0 || d > 20) out.push(" ");
        else {
          const col = d === 0 ? [255, 255, 255] as RGB : hsv((x / cols + t * 0.05) % 1, 0.9, 1 - d / 21);
          out.push(fg(col, c), glyphs[Math.floor(Math.random() * glyphs.length)]);
        }
      }
    }
    return out.join("");
  };
}

/** Stars flying towards the viewer, in colour. */
function stars(): Frame {
  const s = Array.from({ length: 500 }, () => ({ x: Math.random() * 2 - 1, y: Math.random() * 2 - 1, z: Math.random(), h: Math.random() }));
  let last = 0;
  return (t, cols, rows, c) => {
    const dt = Math.min(0.2, t - last); last = t;
    const out: string[] = ["\x1b[48;5;16m\x1b[2J"];
    for (const p of s) {
      p.z -= dt * 0.35;
      if (p.z <= 0.02) { p.x = Math.random() * 2 - 1; p.y = Math.random() * 2 - 1; p.z = 1; p.h = Math.random(); }
      const col = Math.floor((p.x / p.z + 1) / 2 * cols), row = Math.floor((p.y / p.z + 1) / 2 * rows);
      if (col < 0 || col >= cols || row < 0 || row >= rows) continue;
      out.push(`\x1b[${row + 1};${col + 1}H`, fg(hsv(p.h, 0.6, Math.min(1, 1.15 - p.z)), c), p.z < 0.3 ? "★" : p.z < 0.6 ? "*" : "·");
    }
    return out.join("");
  };
}

export const effects: Record<string, () => Frame> = { plasma: () => plasma, tunnel: () => tunnel, fire, rain, stars };

/** Runs until a key other than n. `frames` stops after that many frames (for tests and pipes). */
export async function screensaver(name: string | undefined, frames?: number): Promise<number> {
  const names = Object.keys(effects);
  let index = name ? names.indexOf(name) : Math.floor(Math.random() * names.length);
  if (index < 0) { console.error(`textnaut: no screensaver ${name}; there are: ${names.join(", ")}`); return 2; }
  const colourterm = (Deno.env.get("COLORTERM") ?? "").toLowerCase();
  const colour: Colour = colourterm.includes("truecolor") || colourterm.includes("24bit") ? "24bit" : "256";
  const encoder = new TextEncoder(), write = (s: string) => Deno.stdout.writeSync(encoder.encode(s));
  const tty = Deno.stdin.isTerminal() && Deno.stdout.isTerminal();
  let running = true, effect = effects[names[index]]();
  const stop = () => { running = false; };
  const signals: Deno.Signal[] = ["SIGINT", "SIGTERM", "SIGHUP"];
  for (const s of signals) Deno.addSignalListener(s, stop);
  const restore = () => {
    for (const s of signals) Deno.removeSignalListener(s, stop);
    write("\x1b[0m\x1b[?25h\x1b[?1049l");
    if (tty) { try { Deno.stdin.setRaw(false); } catch { /* the terminal has gone */ } }
  };
  write("\x1b[?1049h\x1b[?25l\x1b[2J");
  try {
    if (tty) {
      Deno.stdin.setRaw(true);
      (async () => {
        const key = new Uint8Array(16);
        while (running) {
          const n = await Deno.stdin.read(key);
          if (n === null) { running = false; return; }
          if (key[0] === 0x6e) { index = (index + 1) % names.length; effect = effects[names[index]](); write("\x1b[0m\x1b[2J"); }
          else running = false;
        }
      })();
    }
    const start = performance.now();
    for (let n = 0; running && (frames === undefined || n < frames); n++) {
      const begin = performance.now();
      const { columns, rows } = tty ? Deno.consoleSize() : { columns: 80, rows: 24 };
      // Synchronized output, where the terminal has it: a frame appears whole.
      write("\x1b[?2026h" + effect((begin - start) / 1000, columns, rows, colour) + "\x1b[?2026l");
      await new Promise((r) => setTimeout(r, Math.max(1, 33 - (performance.now() - begin))));
    }
  } finally {
    restore();
  }
  return 0;
}
