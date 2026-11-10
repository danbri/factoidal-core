// The screensavers. Each is a function of a surface, the time and the time step; a saver keeps
// its own state and rebuilds it when the surface size changes. Random choices come from the
// seeded generator it is given. No saver reads or shows page text.
import { hsv, type Instance, type Rng, type Saver } from "./saver-core.ts";

const TAU = Math.PI * 2;
const clamp01 = (v: number) => v < 0 ? 0 : v > 1 ? 1 : v;
/** A palette of 256 colours from a function of 0..1. */
function palette(f: (v: number) => [number, number, number]): Uint8Array {
  const out = new Uint8Array(768);
  for (let i = 0; i < 256; i++) { const c = f(i / 255); out[i * 3] = c[0]; out[i * 3 + 1] = c[1]; out[i * 3 + 2] = c[2]; }
  return out;
}
const hueRing = palette((v) => [...hsv(v, 0.85, 0.95)] as [number, number, number]);

// ---------------------------------------------------------------- classics

const plasma = (): Instance => (s, t) => {
  const { w, h, px } = s;
  let i = 0;
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++, i += 3) {
    const u = x / w * 12, v = y / h * 8;
    const n = Math.sin(u + t) + Math.sin(v * 1.3 - t * 0.7) + Math.sin((u + v + t) * 0.7) + Math.sin(Math.hypot(u - 6, v - 4) * 1.6 - t * 1.4);
    const k = Math.floor(((n / 8 + 0.5 + t * 0.05) % 1 + 1) % 1 * 255) * 3;
    px[i] = hueRing[k]; px[i + 1] = hueRing[k + 1]; px[i + 2] = hueRing[k + 2];
  }
};

const tunnel = (): Instance => {
  let w = 0, h = 0, radius = new Float32Array(0), angle = new Float32Array(0);
  return (s, t) => {
    if (s.w !== w || s.h !== h) {
      w = s.w; h = s.h; radius = new Float32Array(w * h); angle = new Float32Array(w * h);
      for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
        const dx = (x - w / 2) / h * 2, dy = (y - h / 2) / h * 2;
        radius[y * w + x] = Math.hypot(dx, dy) + 0.001; angle[y * w + x] = Math.atan2(dy, dx) / Math.PI;
      }
    }
    const px = s.px;
    for (let i = 0, p = 0; i < w * h; i++, p += 3) {
      const r = radius[i];
      const check = (Math.floor(1 / r * 3 + t * 3) + Math.floor(angle[i] * 6 + t * 0.6)) % 2 === 0;
      const c = hsv((1 / r * 0.1 + t * 0.08) % 1, 0.8, Math.min(1, r * 1.4) * (check ? 1 : 0.35));
      px[p] = c[0]; px[p + 1] = c[1]; px[p + 2] = c[2];
    }
  };
};

const firePalette = palette((v) => { const x = v * 255; return [Math.min(255, x * 3), Math.max(0, Math.min(255, x * 3 - 255)), Math.max(0, Math.min(255, x * 3 - 510))]; });
function fire(rng: Rng): Instance {
  let w = 0, h = 0, heat = new Float32Array(0);
  return (s) => {
    if (s.w !== w || s.h !== h) { w = s.w; h = s.h; heat = new Float32Array(w * h); }
    for (let x = 0; x < w; x++) heat[(h - 1) * w + x] = rng() < 0.6 ? 255 : 90;
    for (let y = 0; y < h - 1; y++) for (let x = 0; x < w; x++) {
      const below = heat[(y + 1) * w + x], l = heat[(y + 1) * w + (x + w - 1) % w], r = heat[(y + 1) * w + (x + 1) % w], far = heat[Math.min(h - 1, y + 2) * w + x];
      heat[y * w + x] = Math.max(0, (below + l + r + far) / 4 - 1.1 - 40 / h);
    }
    const px = s.px;
    for (let i = 0, p = 0; i < w * h; i++, p += 3) {
      const k = Math.min(255, heat[i] | 0) * 3;
      px[p] = firePalette[k]; px[p + 1] = firePalette[k + 1]; px[p + 2] = firePalette[k + 2];
    }
  };
}

/** Falling glyphs in rainbow columns. */
function rain(rng: Rng): Instance {
  const kana = "ｦｧｨｩｪｱｲｳｴｵｶｷｸｹｺ0123456789FOAFNAUT", plain = "0123456789FOAFNAUTabcdef:=+*<>";
  let drops: number[] = [], speed: number[] = [], seeds: number[] = [];
  return (s, t, dt) => {
    const glyphs = s.utf8 ? kana : plain, { cols, rows } = s;
    if (drops.length !== cols) {
      drops = Array.from({ length: cols }, () => rng() * rows);
      speed = Array.from({ length: cols }, () => 6 + rng() * 22);
      seeds = Array.from({ length: cols }, () => rng());
    }
    for (let x = 0; x < cols; x++) {
      drops[x] += speed[x] * dt;
      if (drops[x] - 22 > rows) { drops[x] = 0; speed[x] = 6 + rng() * 22; }
      const head = Math.floor(drops[x]);
      for (let y = Math.max(0, head - 20); y <= Math.min(rows - 1, head); y++) {
        const d = head - y;
        const c = d === 0 ? [255, 255, 255] : hsv((x / cols + t * 0.05) % 1, 0.9, 1 - d / 21);
        // A glyph changes about four times a second, and not all at once.
        const g = glyphs[Math.floor((Math.sin(x * 12.9 + y * 78.2 + Math.floor(t * 4 + seeds[x] * 9) * 3.7) * 43758.5 % 1 + 1) % 1 * glyphs.length)];
        s.put(x, y, g, c[0], c[1], c[2]);
      }
    }
  };
}

/** Stars flying towards the viewer, in colour. */
function stars(rng: Rng): Instance {
  const field = Array.from({ length: 500 }, () => ({ x: rng() * 2 - 1, y: rng() * 2 - 1, z: rng(), h: rng() }));
  return (s, _t, dt) => {
    for (const p of field) {
      p.z -= dt * 0.35;
      if (p.z <= 0.02) { p.x = rng() * 2 - 1; p.y = rng() * 2 - 1; p.z = 1; p.h = rng(); }
      const col = Math.floor((p.x / p.z + 1) / 2 * s.cols), row = Math.floor((p.y / p.z + 1) / 2 * s.rows);
      if (col < 0 || col >= s.cols || row < 0 || row >= s.rows) continue;
      const c = hsv(p.h, 0.6, Math.min(1, 1.15 - p.z));
      s.put(col, row, s.utf8 ? (p.z < 0.3 ? "★" : p.z < 0.6 ? "*" : "·") : (p.z < 0.3 ? "*" : p.z < 0.6 ? "+" : "."), c[0], c[1], c[2]);
    }
  };
}

// ---------------------------------------------------------------- Conway's Game of Life

function life(rng: Rng): Instance {
  let w = 0, h = 0, cur = new Uint8Array(0), nxt = new Uint8Array(0), age = new Uint8Array(0), glow = new Float32Array(0);
  let acc = 0, steps = 0, repeats = 0, hist: number[] = [];
  const seed = () => {
    const density = 0.25 + rng() * 0.1;
    for (let i = 0; i < cur.length; i++) cur[i] = rng() < density ? 1 : 0;
    age.fill(0); glow.fill(0); hist = []; repeats = 0; steps = 0;
  };
  const step = () => {
    let hash = 2166136261 >>> 0, pop = 0;
    for (let y = 0; y < h; y++) {
      const a = ((y + h - 1) % h) * w, b = y * w, c = ((y + 1) % h) * w;
      for (let x = 0; x < w; x++) {
        const l = (x + w - 1) % w, r = (x + 1) % w;
        const n = cur[a + l] + cur[a + x] + cur[a + r] + cur[b + l] + cur[b + r] + cur[c + l] + cur[c + x] + cur[c + r];
        const alive = cur[b + x] ? (n === 2 || n === 3) : n === 3;
        const i = b + x;
        nxt[i] = alive ? 1 : 0;
        if (alive) { pop++; age[i] = cur[i] ? Math.min(255, age[i] + 1) : 0; hash = Math.imul(hash ^ i, 16777619) >>> 0; }
        else { if (cur[i]) glow[i] = 1; age[i] = 0; }
      }
    }
    [cur, nxt] = [nxt, cur];
    for (let i = 0; i < glow.length; i++) glow[i] *= 0.8;
    steps++;
    if (hist.includes(hash)) repeats++; else repeats = 0;
    hist.push(hash); if (hist.length > 120) hist.shift();
    if (pop === 0 || repeats >= 40 || steps > 1100) seed();
  };
  return (s, _t, dt) => {
    if (s.w !== w || s.h !== h) {
      w = s.w; h = s.h; cur = new Uint8Array(w * h); nxt = new Uint8Array(w * h); age = new Uint8Array(w * h); glow = new Float32Array(w * h); seed();
    }
    acc += dt;
    for (let n = 0; acc >= 1 / 14 && n < 3; n++) { acc -= 1 / 14; step(); }
    if (acc > 0.5) acc = 0;
    const px = s.px;
    for (let i = 0, p = 0; i < w * h; i++, p += 3) {
      if (cur[i]) {
        const a = age[i], c = hsv(0.5 + Math.min(a, 80) * 0.0095, a < 2 ? 0.15 : 0.8, 1);
        px[p] = c[0]; px[p + 1] = c[1]; px[p + 2] = c[2];
      } else if (glow[i] > 0.04) {
        const g = glow[i]; px[p] = 70 * g; px[p + 1] = 25 * g; px[p + 2] = 110 * g;
      }
    }
  };
}

// ---------------------------------------------------------------- snakes

function snakes(rng: Rng): Instance {
  type Snake = { x: number; y: number; dx: number; dy: number; body: number[]; len: number; hue: number; drift: number };
  let w = 0, h = 0, occ = new Uint8Array(0), glowV = new Float32Array(0), glowH = new Float32Array(0), foods: number[] = [], list: Snake[] = [], acc = 0;
  const DIRS = [[1, 0], [0, 1], [-1, 0], [0, -1]];
  const free = (x: number, y: number) => occ[((y + h) % h) * w + ((x + w) % w)] === 0;
  const spawn = (sn?: Snake): Snake => {
    for (let tries = 0; tries < 50; tries++) {
      const x = Math.floor(rng() * w), y = Math.floor(rng() * h);
      if (!occ[y * w + x]) {
        const d = DIRS[Math.floor(rng() * 4)];
        const out = sn ?? { x, y, dx: d[0], dy: d[1], body: [], len: 12, hue: rng(), drift: 0.004 + rng() * 0.01 };
        Object.assign(out, { x, y, dx: d[0], dy: d[1], body: [], len: 18 + Math.floor(rng() * 14), hue: rng() });
        return out;
      }
    }
    return sn ?? { x: 0, y: 0, dx: 1, dy: 0, body: [], len: 8, hue: rng(), drift: 0.006 };
  };
  const food = () => { for (let k = 0; k < 20; k++) { const i = Math.floor(rng() * w * h); if (!occ[i] && !foods.includes(i)) { foods.push(i); return; } } };
  const move = (sn: Snake) => {
    // Head for food in reach, else wander; never into a body.
    let want = [sn.dx, sn.dy];
    let best = 1e9;
    for (const f of foods) {
      const fx = f % w, fy = (f / w) | 0;
      const dx = Math.abs(fx - sn.x) > w / 2 ? (fx > sn.x ? fx - w - sn.x : fx + w - sn.x) : fx - sn.x;
      const dy = Math.abs(fy - sn.y) > h / 2 ? (fy > sn.y ? fy - h - sn.y : fy + h - sn.y) : fy - sn.y;
      const d = Math.abs(dx) + Math.abs(dy);
      if (d < best && d < 24) { best = d; want = Math.abs(dx) > Math.abs(dy) ? [Math.sign(dx), 0] : [0, Math.sign(dy)]; if (want[0] === -sn.dx && want[1] === -sn.dy) want = [sn.dx, sn.dy]; }
    }
    if (best >= 1e9 && rng() < 0.14) want = rng() < 0.5 ? [-sn.dy, sn.dx] : [sn.dy, -sn.dx];
    const options = [want, [sn.dx, sn.dy], [-sn.dy, sn.dx], [sn.dy, -sn.dx]];
    const pick = options.find((o) => !(o[0] === -sn.dx && o[1] === -sn.dy) && free(sn.x + o[0], sn.y + o[1]));
    if (!pick) { for (const i of sn.body) occ[i] = 0; spawn(sn); return; }
    [sn.dx, sn.dy] = pick as [number, number];
    sn.x = (sn.x + sn.dx + w) % w; sn.y = (sn.y + sn.dy + h) % h;
    const i = sn.y * w + sn.x;
    const f = foods.indexOf(i);
    if (f >= 0) { foods.splice(f, 1); sn.len = Math.min(70, sn.len + 4); food(); }
    sn.body.push(i); occ[i] = 1;
    sn.hue += sn.drift;
    while (sn.body.length > sn.len) { const tail = sn.body.shift()!; occ[tail] = 0; glowV[tail] = 0.8; glowH[tail] = sn.hue - sn.body.length * 0.012; }
  };
  return (s, t, dt) => {
    if (s.w !== w || s.h !== h) {
      w = s.w; h = s.h; occ = new Uint8Array(w * h); glowV = new Float32Array(w * h); glowH = new Float32Array(w * h); foods = []; list = [];
      const n = Math.max(2, Math.min(12, Math.round(w * h / 450)));
      for (let i = 0; i < n; i++) list.push(spawn());
      for (let i = 0; i < Math.max(3, n); i++) food();
    }
    acc += dt;
    for (let n = 0; acc >= 1 / 18 && n < 3; n++) {
      acc -= 1 / 18;
      for (const sn of list) move(sn);
      for (let i = 0; i < glowV.length; i++) glowV[i] *= 0.965;
    }
    if (acc > 0.4) acc = 0;
    const px = s.px;
    for (let i = 0; i < w * h; i++) if (glowV[i] > 0.03) { const c = hsv(glowH[i], 0.8, glowV[i]); px[i * 3] = c[0]; px[i * 3 + 1] = c[1]; px[i * 3 + 2] = c[2]; }
    for (const f of foods) { const v = 150 + 105 * Math.sin(t * 8 + f); px[f * 3] = v; px[f * 3 + 1] = v * 0.7; px[f * 3 + 2] = 60; }
    for (const sn of list) {
      const n = sn.body.length;
      sn.body.forEach((i, k) => {
        const c = hsv(sn.hue - (n - k) * 0.012, 0.85, 0.35 + 0.65 * (k + 1) / n);
        px[i * 3] = c[0]; px[i * 3 + 1] = c[1]; px[i * 3 + 2] = c[2];
      });
      const head = sn.body[n - 1];
      if (head !== undefined) { px[head * 3] = 255; px[head * 3 + 1] = 255; px[head * 3 + 2] = 255; }
    }
  };
}

// ---------------------------------------------------------------- Menger sponge, 3D

/** A Menger sponge of the given level as an N*N*N grid (N = 3^level): 1 where there is a cube. */
export function mengerGrid(level: number): { n: number; solid: Uint8Array; count: number } {
  const n = 3 ** level, solid = new Uint8Array(n * n * n);
  let count = 0;
  for (let z = 0; z < n; z++) for (let y = 0; y < n; y++) for (let x = 0; x < n; x++) {
    let middle2 = false;
    for (let k = 1, d = 0; d < level; d++, k *= 3) {
      const m = (Math.floor(x / k) % 3 === 1 ? 1 : 0) + (Math.floor(y / k) % 3 === 1 ? 1 : 0) + (Math.floor(z / k) % 3 === 1 ? 1 : 0);
      if (m >= 2) { middle2 = true; break; }
    }
    if (!middle2) { solid[x + n * (y + n * z)] = 1; count++; }
  }
  return { n, solid, count };
}

/** Object-to-world rotation for the 3D view: Rz * Rx * Ry, row-major. */
function viewMatrix(ay: number, ax: number, az: number): number[] {
  const cy = Math.cos(ay), sy = Math.sin(ay), cx = Math.cos(ax), sx = Math.sin(ax), cz = Math.cos(az), sz = Math.sin(az);
  return [
    cz * cy - sz * sx * sy, -sz * cx, cz * sy + sz * sx * cy,
    sz * cy + cz * sx * sy, cz * cx, sz * sy - cz * sx * cy,
    -cx * sy, sx, cx * cy,
  ];
}

/**
 * Ray-casts an n*n*n voxel cube [-1,1]^3 seen from 4.4 units away, turned by R (object to world).
 * `tag` is 0 for empty and a small number for a voxel. `base` gives a voxel's colour; the
 * cast adds light from the face, ambient and distance fog. One DDA walk per pixel.
 */
function castVoxels(s: { w: number; h: number; px: Uint8ClampedArray }, n: number, tag: Uint8Array, R: number[], base: (tag: number, vx: number, vy: number, vz: number) => [number, number, number], zoom = 1) {
  const { w, h, px } = s;
  const D = 4.4, K = 0.55 / zoom;
  const L = [-0.5, 0.65, -0.57], ll = Math.hypot(L[0], L[1], L[2]);
  const lam = new Float32Array(6); // axis*2 + (sign > 0)
  for (let a = 0; a < 3; a++) for (let sg = 0; sg < 2; sg++) {
    const sign = sg ? 1 : -1;
    lam[a * 2 + sg] = Math.max(0, (R[a] * sign * L[0] + R[3 + a] * sign * L[1] + R[6 + a] * sign * L[2]) / ll);
  }
  // Ray origin in object space: R^T * (0,0,-D).
  const ox = -R[6] * D, oy = -R[7] * D, oz = -R[8] * D, cell = 2 / n;
  for (let py = 0; py < h; py++) {
    const vy = -((py + 0.5 - h / 2) / (h / 2)) * K, bgv = py / h;
    for (let pxl = 0; pxl < w; pxl++) {
      const ux = ((pxl + 0.5 - w / 2) / (h / 2)) * K, p = (py * w + pxl) * 3;
      // Ray direction in object space: R^T * (ux, vy, 1).
      const dx = R[0] * ux + R[3] * vy + R[6], dy = R[1] * ux + R[4] * vy + R[7], dz = R[2] * ux + R[5] * vy + R[8];
      const ix = 1 / (dx || 1e-9), iy = 1 / (dy || 1e-9), iz = 1 / (dz || 1e-9);
      let t0x = (-1 - ox) * ix, t1x = (1 - ox) * ix; if (t0x > t1x) { const q = t0x; t0x = t1x; t1x = q; }
      let t0y = (-1 - oy) * iy, t1y = (1 - oy) * iy; if (t0y > t1y) { const q = t0y; t0y = t1y; t1y = q; }
      let t0z = (-1 - oz) * iz, t1z = (1 - oz) * iz; if (t0z > t1z) { const q = t0z; t0z = t1z; t1z = q; }
      let tin = t0x, axis = 0;
      if (t0y > tin) { tin = t0y; axis = 1; }
      if (t0z > tin) { tin = t0z; axis = 2; }
      const tout = Math.min(t1x, t1y, t1z);
      if (tin >= tout) { px[p] = 6 + 8 * bgv; px[p + 1] = 8 + 4 * bgv; px[p + 2] = 22 + 22 * bgv; continue; }
      let vx = Math.min(n - 1, Math.max(0, Math.floor((ox + dx * tin + 1) / cell))), vyy = Math.min(n - 1, Math.max(0, Math.floor((oy + dy * tin + 1) / cell))), vz = Math.min(n - 1, Math.max(0, Math.floor((oz + dz * tin + 1) / cell)));
      const stx = dx > 0 ? 1 : -1, sty = dy > 0 ? 1 : -1, stz = dz > 0 ? 1 : -1;
      const tdx = Math.abs(cell * ix), tdy = Math.abs(cell * iy), tdz = Math.abs(cell * iz);
      let tmx = ((vx + (stx > 0 ? 1 : 0)) * cell - 1 - ox) * ix, tmy = ((vyy + (sty > 0 ? 1 : 0)) * cell - 1 - oy) * iy, tmz = ((vz + (stz > 0 ? 1 : 0)) * cell - 1 - oz) * iz;
      let hit = 0, th = tin, sign = axis === 0 ? stx : axis === 1 ? sty : stz;
      for (let guard = 0; guard < 3 * n + 3; guard++) {
        const v = tag[vx + n * (vyy + n * vz)];
        if (v) { hit = v; break; }
        if (tmx < tmy && tmx < tmz) { th = tmx; tmx += tdx; vx += stx; axis = 0; sign = stx; if (vx < 0 || vx >= n) break; }
        else if (tmy < tmz) { th = tmy; tmy += tdy; vyy += sty; axis = 1; sign = sty; if (vyy < 0 || vyy >= n) break; }
        else { th = tmz; tmz += tdz; vz += stz; axis = 2; sign = stz; if (vz < 0 || vz >= n) break; }
      }
      if (!hit) { px[p] = 6 + 8 * bgv; px[p + 1] = 8 + 4 * bgv; px[p + 2] = 22 + 22 * bgv; continue; }
      // The face we crossed faces against the ray: its outward normal is -sign on that axis.
      const l = lam[axis * 2 + (sign > 0 ? 0 : 1)], fog = clamp01(1.35 - 0.11 * th), c = base(hit, vx, vyy, vz), amb = 0.22;
      px[p] = (c[0] * l + 40 * amb) * fog + 6; px[p + 1] = (c[1] * l + 70 * amb) * fog + 8; px[p + 2] = (c[2] * l * 0.8 + 130 * amb) * fog + 20;
    }
  }
}

function sponge(): Instance {
  let level = 0, grid = mengerGrid(2), n = 0;
  return (s, t) => {
    const want = s.h < 84 ? 2 : 3;
    if (want !== level) { level = want; grid = mengerGrid(level); n = grid.n; }
    castVoxels(s, n, grid.solid, viewMatrix(t * 0.5, 0.45 + 0.3 * Math.sin(t * 0.31), 0.15 * Math.sin(t * 0.23)), (_v, x, y, z) => hsv(0.09 + 0.1 * (x + y + z) / (3 * n) + 0.02 * ((x + y) % 3), 0.62, 1), 1.12);
  };
}

// ---------------------------------------------------------------- Menger sponge, 4D

export type Vec4 = [number, number, number, number];
/** Rotates in the XW plane by `a`, then in the YW plane by `b`, then in the ZW plane by `c`. A rotation keeps length. */
export function rotate4(p: Vec4, a: number, b: number, c = 0): Vec4 {
  let [x, y, z, w] = p;
  let co = Math.cos(a), si = Math.sin(a); [x, w] = [x * co - w * si, x * si + w * co];
  co = Math.cos(b); si = Math.sin(b); [y, w] = [y * co - w * si, y * si + w * co];
  co = Math.cos(c); si = Math.sin(c); [z, w] = [z * co - w * si, z * si + w * co];
  return [x, y, z, w];
}

/** The 4D Menger sponge's kept cells: a cell of the 3^L grid stays when, at every level, at most one of its four base-3 digits is the middle one (48 of 81 per step). */
export function mengerCells4(level: number): { n: number; cells: Uint8Array; count: number } {
  const n = 3 ** level, cells = new Uint8Array(n ** 4);
  let count = 0;
  for (let i = 0; i < n ** 4; i++) {
    let ok = true;
    for (let k = 1, d = 0; d < level && ok; d++, k *= 3) {
      let middle = 0, rest = i;
      for (let axis = 0; axis < 4; axis++) { if (Math.floor((rest % n) / k) % 3 === 1) middle++; rest = Math.floor(rest / n); }
      if (middle >= 2) ok = false;
    }
    if (ok) { cells[i] = 1; count++; }
  }
  return { n, cells, count };
}

/** The inverse of `rotate4`: the three planes undone in the opposite order. */
export function unrotate4(p: Vec4, a: number, b: number, c = 0): Vec4 {
  let [x, y, z, w] = p;
  let co = Math.cos(c), si = Math.sin(c); [z, w] = [z * co + w * si, -z * si + w * co];
  co = Math.cos(b); si = Math.sin(b); [y, w] = [y * co + w * si, -y * si + w * co];
  co = Math.cos(a); si = Math.sin(a); [x, w] = [x * co + w * si, -x * si + w * co];
  return [x, y, z, w];
}

const W_COLOURS: [number, number, number][] = Array.from({ length: 256 }, (_, i) => [...hsv(0.68 - 0.68 * i / 255, 0.85, 1)] as [number, number, number]);

/**
 * The 4D Menger sponge (level 2: 2304 of 6561 hypercells) turning in the XW and YW planes. The
 * eye is in 4D at w = D4. Each voxel of a 3D "retina" cube looks along a 4D ray: the first
 * hypercell it meets within a slab of W (nearest the eye first) fills the voxel and sets its
 * colour by that W: red near the eye, blue far. The retina cube is then ray-cast and lit like the
 * 3D sponge, so parts of the sponge come and go as the turn carries them through the slab.
 */
function sponge4d(): Instance {
  const model = mengerCells4(2), cells = model.cells, n4 = model.n;
  let tag = new Uint8Array(0), size = 0;
  return (s, t) => {
    const N = s.h < 100 ? 22 : 32, SAMPLES = 14, D4 = 4, E = 1.9, WMIN = -0.8, WMAX = 0.8;
    if (N !== size) { size = N; tag = new Uint8Array(N * N * N); }
    const a = t * 0.5, b = t * 0.33, c = 0.18 * Math.sin(t * 0.2);
    // The inverse rotation as a matrix: columns are the images of the unit vectors.
    const cols: Vec4[] = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]].map((e) => unrotate4(e as Vec4, a, b, c));
    const cell = 2 * E / N;
    for (let z = 0; z < N; z++) for (let y = 0; y < N; y++) for (let x = 0; x < N; x++) {
      const rx = -E + (x + 0.5) * cell, ry = -E + (y + 0.5) * cell, rz = -E + (z + 0.5) * cell;
      // Object coordinates of the 4D point (rx*k, ry*k, rz*k, w), k = (D4 - w) / D4, are k*A + w*B.
      const Ax = cols[0][0] * rx + cols[1][0] * ry + cols[2][0] * rz, Ay = cols[0][1] * rx + cols[1][1] * ry + cols[2][1] * rz;
      const Az = cols[0][2] * rx + cols[1][2] * ry + cols[2][2] * rz, Aw = cols[0][3] * rx + cols[1][3] * ry + cols[2][3] * rz;
      const Bx = cols[3][0], By = cols[3][1], Bz = cols[3][2], Bw = cols[3][3];
      let found = 0;
      for (let i = 0; i < SAMPLES; i++) {
        const w = WMAX - (WMAX - WMIN) * (i + 0.5) / SAMPLES, k = (D4 - w) / D4;
        const X = k * Ax + w * Bx, Y = k * Ay + w * By, Z = k * Az + w * Bz, W = k * Aw + w * Bw;
        if (X < -1 || X >= 1 || Y < -1 || Y >= 1 || Z < -1 || Z >= 1 || W < -1 || W >= 1) continue;
        if (cells[(((X + 1) / 2 * n4) | 0) + n4 * ((((Y + 1) / 2 * n4) | 0) + n4 * ((((Z + 1) / 2 * n4) | 0) + n4 * (((W + 1) / 2 * n4) | 0)))]) { found = 1 + Math.round(254 * (w - WMIN) / (WMAX - WMIN)); break; }
      }
      tag[x + N * (y + N * z)] = found;
    }
    // Tag 255 is nearest the eye in W (red), tag 1 farthest (blue).
    castVoxels(s, N, tag, viewMatrix(t * 0.21, 0.5, 0), (v) => W_COLOURS[v], 1.25);
  };
}

// ---------------------------------------------------------------- Lissajous

function lissajous(): Instance {
  let w = 0, h = 0, glow = new Float32Array(0);
  const knee = new Float32Array(1024);
  for (let i = 0; i < 1024; i++) knee[i] = 255 * (1 - Math.exp(-i / 200));
  return (s, t, dt) => {
    if (s.w !== w || s.h !== h) { w = s.w; h = s.h; glow = new Float32Array(w * h * 3); }
    const keep = Math.pow(0.02, dt);
    for (let i = 0; i < glow.length; i++) glow[i] *= keep;
    const curves = [[3, 2, 0.31], [5, 4, 0.23], [2, 3, 0.17]];
    curves.forEach(([a, b, speed], k) => {
      const ph = t * speed * 2 + k * 2.1, N = Math.min(2500, Math.max(300, (w + h) * 5));
      let lx = 0, ly = 0;
      for (let i = 0; i <= N; i++) {
        const th = i / N * TAU;
        const amp = 0.46 + 0.04 * Math.sin(t * 0.7 + k);
        const x = w / 2 + Math.sin(a * th + ph) * w * amp, y = h / 2 + Math.sin(b * th + ph * 0.6) * h * amp;
        if (i > 0) {
          const steps = Math.min(40, Math.ceil(Math.max(Math.abs(x - lx), Math.abs(y - ly))));
          const col = hsv(th / TAU * 0.5 + t * 0.07 + k * 0.33, 0.8, 1);
          for (let q = 1; q <= steps; q++) {
            const px = Math.round(lx + (x - lx) * q / steps), py = Math.round(ly + (y - ly) * q / steps);
            if (px < 0 || py < 0 || px >= w || py >= h) continue;
            const o = (py * w + px) * 3;
            glow[o] += col[0] * 0.07; glow[o + 1] += col[1] * 0.07; glow[o + 2] += col[2] * 0.07;
          }
        }
        lx = x; ly = y;
      }
    });
    const px = s.px;
    for (let i = 0; i < glow.length; i++) px[i] = knee[Math.min(1023, glow[i] | 0)];
  };
}

// ---------------------------------------------------------------- metaballs

function metaballs(): Instance {
  return (s, t) => {
    const { w, h, px } = s, aspect = w / h;
    const balls = Array.from({ length: 7 }, (_, i) => ({
      x: aspect * (0.5 + 0.38 * Math.sin(t * (0.4 + i * 0.11) + i * 1.7)), y: 0.5 + 0.34 * Math.cos(t * (0.33 + i * 0.09) + i * 2.3), r: 0.05 + 0.02 * (i % 3),
    }));
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const fx = x / h, fy = y / h;
      let f = 0;
      for (const b of balls) { const dx = fx - b.x, dy = fy - b.y; f += b.r * b.r / (dx * dx + dy * dy + 1e-5) * 1.0; }
      const p = (y * w + x) * 3;
      if (f < 1) { const g = f * f * 0.5; px[p] = 10 + 40 * g; px[p + 1] = 6 + 20 * g; px[p + 2] = 30 + 90 * g; }
      else {
        const c = hsv(0.9 + 0.12 * Math.min(f, 6) / 6 + t * 0.03, 0.75 - 0.35 * clamp01((f - 2) / 3), 0.8 + 0.2 * clamp01(f / 3));
        px[p] = c[0]; px[p + 1] = c[1]; px[p + 2] = c[2];
      }
    }
  };
}

// ---------------------------------------------------------------- spinning torus

function torus(): Instance {
  let zb = new Float32Array(0), lum = new Float32Array(0), hue = new Float32Array(0);
  return (s, t) => {
    const { w, h, px } = s;
    if (zb.length !== w * h) { zb = new Float32Array(w * h); lum = new Float32Array(w * h); hue = new Float32Array(w * h); }
    zb.fill(0);
    const A = t * 0.8, B = t * 0.55, ca = Math.cos(A), sa = Math.sin(A), cb = Math.cos(B), sb = Math.sin(B);
    // Rotation about X by A then about Z by B.
    const m = [cb, -sb * ca, sb * sa, sb, cb * ca, -cb * sa, 0, sa, ca];
    const R1 = 1, R2 = 2, K2 = 5, k1 = Math.min(h * 0.77, w * 0.5 * 5 / 3 * 0.9);
    const nT = Math.min(300, Math.max(24, Math.ceil(TAU * k1 / 5 * 1.8))), nP = Math.min(900, Math.max(48, Math.ceil(TAU * 3 * k1 / 5 * 1.8)));
    const cosT = new Float32Array(nT), sinT = new Float32Array(nT);
    for (let i = 0; i < nT; i++) { cosT[i] = Math.cos(i / nT * TAU); sinT[i] = Math.sin(i / nT * TAU); }
    const Lx = 0, Ly = 0.7, Lz = -0.7;
    for (let j = 0; j < nP; j++) {
      const phi = j / nP * TAU, cp = Math.cos(phi), sp = Math.sin(phi);
      for (let i = 0; i < nT; i++) {
        const ct = cosT[i], st = sinT[i], ring = R2 + R1 * ct;
        const x0 = ring * cp, y0 = ring * sp, z0 = R1 * st;
        const x = m[0] * x0 + m[1] * y0 + m[2] * z0, y = m[3] * x0 + m[4] * y0 + m[5] * z0, z = m[6] * x0 + m[7] * y0 + m[8] * z0;
        const ooz = 1 / (K2 + z), X = Math.round(w / 2 + k1 * x * ooz), Y = Math.round(h / 2 - k1 * y * ooz);
        if (X < 0 || Y < 0 || X >= w || Y >= h) continue;
        const idx = Y * w + X;
        if (ooz <= zb[idx]) continue;
        const nx0 = ct * cp, ny0 = ct * sp, nz0 = st;
        const nx = m[0] * nx0 + m[1] * ny0 + m[2] * nz0, ny = m[3] * nx0 + m[4] * ny0 + m[5] * nz0, nz = m[6] * nx0 + m[7] * ny0 + m[8] * nz0;
        zb[idx] = ooz; lum[idx] = nx * Lx + ny * Ly + nz * Lz; hue[idx] = i / nT + j / nP * 2;
      }
    }
    for (let i = 0, p = 0; i < w * h; i++, p += 3) {
      if (!zb[i]) { const v = 4 + 10 * (i / (w * h)); px[p] = v; px[p + 1] = v; px[p + 2] = v * 2.4; continue; }
      const l = lum[i], d = Math.max(0, l), spec = Math.pow(d, 14);
      const c = hsv(hue[i] + t * 0.05, 0.75 - 0.5 * spec, 0.14 + 0.86 * d);
      px[p] = c[0] + 140 * spec; px[p + 1] = c[1] + 140 * spec; px[p + 2] = c[2] + 140 * spec;
    }
  };
}

// ---------------------------------------------------------------- water ripples

const waterPalette = palette((v) => {
  if (v < 0.5) { const k = v / 0.5; return [4 + 6 * k, 14 + 50 * k, 50 + 100 * k]; }
  const k = (v - 0.5) / 0.5; return [10 + 235 * k, 64 + 180 * k, 150 + 100 * k];
});
function waves(rng: Rng): Instance {
  let w = 0, h = 0, cur = new Float32Array(0), prev = new Float32Array(0), drop = 0;
  return (s, _t, dt) => {
    if (s.w !== w || s.h !== h) { w = s.w; h = s.h; cur = new Float32Array(w * h); prev = new Float32Array(w * h); drop = 0; }
    if (w < 3 || h < 3) return;
    drop -= dt;
    if (drop <= 0) {
      drop = 0.25 + rng() * 0.7;
      const cx = 1 + Math.floor(rng() * (w - 2)), cy = 1 + Math.floor(rng() * (h - 2)), rad = 1 + Math.floor(rng() * 2);
      for (let y = -rad; y <= rad; y++) for (let x = -rad; x <= rad; x++) {
        const X = cx + x, Y = cy + y;
        if (X > 0 && Y > 0 && X < w - 1 && Y < h - 1) cur[Y * w + X] += 6 - 2 * Math.hypot(x, y);
      }
    }
    for (let pass = 0; pass < 2; pass++) {
      for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
        const i = y * w + x;
        prev[i] = (2 * cur[i] - prev[i] + 0.45 * (cur[i - 1] + cur[i + 1] + cur[i - w] + cur[i + w] - 4 * cur[i])) * 0.992;
      }
      [cur, prev] = [prev, cur];
    }
    const px = s.px;
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const i = y * w + x, hh = cur[i];
      const slope = x > 0 && x < w - 1 && y > 0 ? (cur[i + 1] - cur[i - 1]) * 0.6 + (cur[i] - cur[i - w]) * 0.6 : 0;
      const v = Math.min(255, Math.max(0, 128 + hh * 14 + slope * 40)) | 0;
      const k = v * 3, p = i * 3;
      px[p] = waterPalette[k]; px[p + 1] = waterPalette[k + 1]; px[p + 2] = waterPalette[k + 2];
    }
  };
}

// ---------------------------------------------------------------- maze

function maze(rng: Rng): Instance {
  let w = 0, h = 0, cw = 0, ch = 0, ox = 0, oy = 0, open = new Uint8Array(0), dist = new Int32Array(0), parent = new Int32Array(0), mark = new Uint8Array(0);
  let phase: "carve" | "flood" | "trace" | "hold" = "carve", stack: number[] = [], queue: number[] = [], qi = 0, path: number[] = [], shown = 0, hold = 0, maxd = 1;
  const pid = (cx: number, cy: number) => (oy + 1 + 2 * cy) * w + ox + 1 + 2 * cx;
  const build = () => {
    open.fill(0); dist.fill(-1); parent.fill(-1); mark.fill(0); stack = []; queue = []; qi = 0; path = []; shown = 0; maxd = 1; phase = "carve";
    const start = pid(0, 0); open[start] = 1; stack.push(0);
  };
  return (s, t, dt) => {
    if (s.w !== w || s.h !== h) {
      w = s.w; h = s.h; cw = Math.floor((w - 1) / 2); ch = Math.floor((h - 1) / 2);
      ox = (w - (2 * cw + 1)) >> 1; oy = (h - (2 * ch + 1)) >> 1;
      open = new Uint8Array(w * h); dist = new Int32Array(w * h); parent = new Int32Array(w * h); mark = new Uint8Array(w * h);
      if (cw >= 2 && ch >= 2) build();
    }
    const px = s.px;
    if (cw < 2 || ch < 2) return;
    if (phase === "carve") {
      const per = Math.max(1, Math.ceil(cw * ch / 200));
      for (let n = 0; n < per && stack.length; n++) {
        const top = stack[stack.length - 1], cx = top % cw, cy = (top / cw) | 0;
        const nb: number[] = [];
        if (cx > 0 && !open[pid(cx - 1, cy)]) nb.push(0);
        if (cx < cw - 1 && !open[pid(cx + 1, cy)]) nb.push(1);
        if (cy > 0 && !open[pid(cx, cy - 1)]) nb.push(2);
        if (cy < ch - 1 && !open[pid(cx, cy + 1)]) nb.push(3);
        if (!nb.length) { stack.pop(); continue; }
        const d = nb[Math.floor(rng() * nb.length)], dx = d === 0 ? -1 : d === 1 ? 1 : 0, dy = d === 2 ? -1 : d === 3 ? 1 : 0;
        open[pid(cx, cy) + dy * w + dx] = 1; open[pid(cx + dx, cy + dy)] = 1;
        stack.push((cy + dy) * cw + cx + dx);
      }
      if (!stack.length) { phase = "flood"; const st = pid(0, 0); dist[st] = 0; queue = [st]; qi = 0; }
    } else if (phase === "flood") {
      const per = Math.max(2, Math.ceil(cw * ch * 4 / 160));
      for (let n = 0; n < per && qi < queue.length; n++) {
        const i = queue[qi++];
        for (const o of [1, -1, w, -w]) {
          const j = i + o;
          if (j >= 0 && j < w * h && open[j] && dist[j] < 0 && !((o === 1 && (i % w) === w - 1) || (o === -1 && (i % w) === 0))) { dist[j] = dist[i] + 1; parent[j] = i; queue.push(j); if (dist[j] > maxd) maxd = dist[j]; }
        }
      }
      if (qi >= queue.length) {
        phase = "trace"; path = [];
        for (let i = pid(cw - 1, ch - 1); i >= 0; i = parent[i]) path.push(i);
        path.reverse(); shown = 0;
      }
    } else if (phase === "trace") {
      shown += Math.max(2, Math.ceil(path.length / 90));
      if (shown >= path.length) { phase = "hold"; hold = 3.5; }
    } else { hold -= dt; if (hold <= 0) build(); }
    // Walls, passages, the flood and the path.
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const i = y * w + x, p = i * 3;
      const inside = x >= ox && x < ox + 2 * cw + 1 && y >= oy && y < oy + 2 * ch + 1;
      if (!inside) { px[p] = 4; px[p + 1] = 4; px[p + 2] = 12; continue; }
      if (!open[i]) { px[p] = 28; px[p + 1] = 30; px[p + 2] = 72; continue; }
      if (dist[i] >= 0) { const c = hsv(0.95 - 0.8 * dist[i] / maxd + t * 0.02, 0.8, 0.85); px[p] = c[0]; px[p + 1] = c[1]; px[p + 2] = c[2]; }
      else { px[p] = 8; px[p + 1] = 14; px[p + 2] = 20; }
    }
    if (phase === "carve") {
      const n = stack.length;
      stack.forEach((c, k) => { const i = pid(c % cw, (c / cw) | 0) * 3; const v = 0.35 + 0.65 * k / n; px[i] = 200 * v; px[i + 1] = 60 * v; px[i + 2] = 160 * v; });
      if (n) { const c = stack[n - 1], i = pid(c % cw, (c / cw) | 0) * 3; px[i] = 255; px[i + 1] = 255; px[i + 2] = 255; }
    }
    for (let k = 0; k < Math.min(shown, path.length); k++) { const i = path[k] * 3; px[i] = 255; px[i + 1] = 245; px[i + 2] = 200; }
  };
}

// ---------------------------------------------------------------- cyclic cellular automaton

function cyclic(rng: Rng): Instance {
  const STATES = 14, THRESH = 1;
  let w = 0, h = 0, cur = new Uint8Array(0), nxt = new Uint8Array(0), age = 0;
  const seed = () => { for (let i = 0; i < cur.length; i++) cur[i] = Math.floor(rng() * STATES); age = 0; };
  return (s, _t, dt) => {
    if (s.w !== w || s.h !== h) { w = s.w; h = s.h; cur = new Uint8Array(w * h); nxt = new Uint8Array(w * h); seed(); }
    age += dt;
    if (age > 45) seed();
    for (let y = 0; y < h; y++) {
      const a = ((y + h - 1) % h) * w, b = y * w, c = ((y + 1) % h) * w;
      for (let x = 0; x < w; x++) {
        const l = (x + w - 1) % w, r = (x + 1) % w, v = cur[b + x], want = v + 1 === STATES ? 0 : v + 1;
        const n = (cur[a + l] === want ? 1 : 0) + (cur[a + x] === want ? 1 : 0) + (cur[a + r] === want ? 1 : 0) + (cur[b + l] === want ? 1 : 0) + (cur[b + r] === want ? 1 : 0) + (cur[c + l] === want ? 1 : 0) + (cur[c + x] === want ? 1 : 0) + (cur[c + r] === want ? 1 : 0);
        nxt[b + x] = n >= THRESH ? want : v;
      }
    }
    [cur, nxt] = [nxt, cur];
    const px = s.px;
    for (let i = 0, p = 0; i < w * h; i++, p += 3) {
      const v = cur[i] / STATES, c = hsv(v + age * 0.02, 0.85, 0.35 + 0.65 * v);
      px[p] = c[0]; px[p + 1] = c[1]; px[p + 2] = c[2];
    }
  };
}

// ---------------------------------------------------------------- Christmas scenes (hidden)

type Flake = { x: number; y: number; d: number; ph: number };
/** Snow that falls and settles on whatever is solid, sliding down slopes like sand. */
class Snowfall {
  flakes: Flake[] = [];
  settled: Uint8Array;
  count = 0;
  constructor(private w: number, private h: number, private solid: Uint8Array, private rng: Rng, amount: number) {
    this.settled = new Uint8Array(w * h);
    for (let i = 0; i < amount; i++) this.flakes.push({ x: rng() * w, y: rng() * h, d: 0.45 + rng() * 0.55, ph: rng() * TAU });
  }
  step(dt: number, t: number) {
    const { w, h, solid, settled } = this;
    for (const f of this.flakes) {
      f.y += (h * 0.1 + h * 0.12 * f.d) * dt;
      f.x += Math.sin(t * 1.3 + f.ph) * 3 * f.d * dt * (h / 40);
      if (f.x < 0) f.x += w; else if (f.x >= w) f.x -= w;
      let ix = Math.floor(f.x), iy = Math.floor(f.y);
      if (iy < 0) continue;
      const blocked = (x: number, y: number) => y >= h || (x >= 0 && x < w && y >= 0 && (solid[y * w + x] || settled[y * w + x]) === 1);
      if (iy >= h || blocked(ix, iy + 1) || blocked(ix, iy)) {
        if (iy >= h) iy = h - 1;
        // Slide off a slope, else stay.
        let moved = true;
        for (let guard = 0; guard < 6 && moved; guard++) {
          moved = false;
          if (blocked(ix, iy)) { iy--; if (iy < 0) break; }
          if (!blocked(ix, iy + 1)) { iy++; moved = true; continue; }
          const dir = this.rng() < 0.5 ? -1 : 1;
          if (ix + dir >= 0 && ix + dir < w && !blocked(ix + dir, iy + 1) && !blocked(ix + dir, iy)) { ix += dir; iy++; moved = true; }
          else if (ix - dir >= 0 && ix - dir < w && !blocked(ix - dir, iy + 1) && !blocked(ix - dir, iy)) { ix -= dir; iy++; moved = true; }
        }
        if (iy >= 0 && iy < h && !blocked(ix, iy) && !settled[iy * w + ix]) { settled[iy * w + ix] = 1; this.count++; }
        f.x = this.rng() * w; f.y = -this.rng() * h * 0.2;
      }
    }
    // Too much snow: it melts away in places.
    if (this.count > w * h * 0.05) {
      for (let k = 0; k < Math.ceil(this.count / 40); k++) { const i = Math.floor(this.rng() * w * h); if (settled[i]) { settled[i] = 0; this.count--; } }
    }
  }
}

function christmasTree(rng: Rng): Instance {
  let w = 0, h = 0, scene = new Uint8ClampedArray(0), solid = new Uint8Array(0), snow: Snowfall | null = null;
  let twinkles: { x: number; y: number; ph: number }[] = [], lights: { x: number; y: number; hue: number; ph: number }[] = [];
  let star = { x: 0, y: 0 }, windowAt: { x: number; y: number } | null = null, baubles: { x: number; y: number; hue: number }[] = [];
  const put = (x: number, y: number, r: number, g: number, b: number) => {
    x = Math.round(x); y = Math.round(y);
    if (x < 0 || y < 0 || x >= w || y >= h) return;
    const i = (y * w + x) * 3; scene[i] = r; scene[i + 1] = g; scene[i + 2] = b;
  };
  const rect = (x0: number, y0: number, x1: number, y1: number, r: number, g: number, b: number, hard = false) => {
    for (let y = Math.floor(y0); y < Math.ceil(y1); y++) for (let x = Math.floor(x0); x < Math.ceil(x1); x++) { put(x, y, r, g, b); if (hard && x >= 0 && y >= 0 && x < w && y < h) solid[y * w + x] = 1; }
  };
  const build = () => {
    scene = new Uint8ClampedArray(w * h * 3); solid = new Uint8Array(w * h);
    const ground = (x: number) => h * 0.82 + Math.sin(x * 0.07) * h * 0.015 + Math.sin(x * 0.019 + 1) * h * 0.03;
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const k = y / h, i = (y * w + x) * 3;
      scene[i] = 5 + 30 * k * k; scene[i + 1] = 7 + 26 * k * k; scene[i + 2] = 30 + 60 * k;
    }
    // Moon and its halo.
    const mx = w * 0.84, my = h * 0.2, mr = Math.max(1.6, h * 0.065);
    for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
      const d = Math.hypot(x - mx, y - my), i = (y * w + x) * 3;
      if (d < mr) { scene[i] = 238; scene[i + 1] = 238; scene[i + 2] = 215; }
      else if (d < mr * 4) { const g = Math.pow(1 - (d - mr) / (mr * 3), 2) * 0.35; scene[i] += 90 * g; scene[i + 1] += 100 * g; scene[i + 2] += 110 * g; }
    }
    // Far hills, then snowy ground.
    for (let x = 0; x < w; x++) {
      const far = h * 0.7 + Math.sin(x * 0.04 + 2) * h * 0.04;
      for (let y = Math.max(0, Math.floor(far)); y < h; y++) put(x, y, 40, 52, 100);
      const g = ground(x);
      for (let y = Math.max(0, Math.floor(g)); y < h; y++) {
        const k = (y - g) / Math.max(1, h - g);
        put(x, y, 226 - 70 * k, 233 - 60 * k, 248 - 30 * k); solid[y * w + x] = 1;
      }
    }
    twinkles = [];
    for (let i = 0; i < w * h / 220; i++) { const x = Math.floor(rng() * w), y = Math.floor(rng() * h * 0.6); if (Math.hypot(x - mx, y - my) > mr * 2) twinkles.push({ x, y, ph: rng() * TAU }); }
    // A house with a lit window.
    windowAt = null;
    if (w > 70 && h > 40) {
      const hx = w * 0.13, hw = h * 0.26, hh = h * 0.17, gy = ground(hx + hw / 2);
      rect(hx, gy - hh, hx + hw, gy + 1, 66, 42, 44, true);
      for (let r = 0; r < hh * 0.55; r++) { const half = hw / 2 + 1 - r * (hw / 2 + 1) / (hh * 0.55); rect(hx + hw / 2 - half, gy - hh - r, hx + hw / 2 + half, gy - hh - r + 1, r < 2 ? 235 : 52, r < 2 ? 238 : 36, r < 2 ? 250 : 48, true); }
      rect(hx + hw * 0.62, gy - hh * 0.8, hx + hw * 0.62 + hw * 0.18 + 1, gy - hh * 0.8 + Math.max(2, hh * 0.3), 255, 196, 84);
      rect(hx + hw * 0.12, gy - hh * 0.45, hx + hw * 0.3, gy, 30, 20, 20);
      windowAt = { x: hx + hw * 0.62 + hw * 0.09, y: gy - hh * 0.8 + hh * 0.15 };
    }
    // The tree: four tiers and a trunk.
    const cx = w * (windowAt ? 0.58 : 0.5), base = ground(cx) + 1, H = Math.min(h * 0.68, w * 0.7);
    const top = base - H, tiers = [[0.0, 0.34, 0.15], [0.17, 0.52, 0.22], [0.34, 0.7, 0.29], [0.52, 0.9, 0.36]];
    rect(cx - H * 0.035, base - H * 0.14, cx + H * 0.035 + 1, base + 1, 70, 44, 30, true);
    const mask = new Uint8Array(w * h);
    tiers.forEach(([a, b, hw], tier) => {
      const y0 = top + a * H, y1 = top + b * H;
      for (let y = Math.floor(y0); y <= Math.ceil(y1); y++) {
        const u = (y - y0) / Math.max(1, y1 - y0), half = H * hw * u + (((y * 7 + tier * 3) % 3) - 1) * H * 0.006 * u;
        for (let x = Math.floor(cx - half); x <= Math.ceil(cx + half); x++) {
          if (x < 0 || y < 0 || x >= w || y >= h) continue;
          const shade = 0.6 + 0.4 * (1 - u * 0.7) + ((x * 13 + y * 7) % 5) * 0.03 - (x < cx ? 0 : 0.08);
          put(x, y, 12 + 14 * shade, 70 * shade + 20, 36 * shade + 10); solid[y * w + x] = 1; mask[y * w + x] = 1;
        }
      }
    });
    // Baubles and fairy lights on the tiers.
    baubles = []; lights = [];
    const palette6 = [0.0, 0.12, 0.6, 0.85, 0.33, 0.5];
    tiers.forEach(([a, b, hw], tier) => {
      const y0 = top + a * H, y1 = top + b * H, n = Math.max(3, Math.round(H * hw / (h * 0.045)));
      for (let k = 0; k < n; k++) {
        const u = (k + 0.5) / n, x = cx + (u * 2 - 1) * H * hw * 0.82, y = y1 - H * 0.025 - Math.sin(u * Math.PI) * H * 0.05;
        if (mask[Math.round(y) * w + Math.round(x)]) lights.push({ x, y, hue: palette6[(k + tier) % palette6.length], ph: rng() * TAU });
        const bx = cx + (rng() * 2 - 1) * H * hw * 0.65 * ((y1 - y0) * 0.6 / (y1 - y0 + 1) + 0.3), by = y0 + (0.3 + rng() * 0.6) * (y1 - y0);
        if (mask[Math.round(by) * w + Math.round(bx)]) baubles.push({ x: bx, y: by, hue: palette6[Math.floor(rng() * palette6.length)] });
      }
    });
    star = { x: cx, y: top - 1 };
    // Presents under the tree.
    const gy = base, unit = Math.max(2, H * 0.07);
    [[-0.28, 1.0, 0.1, 0.75, 0.55], [0.2, 1.3, 0.35, 0.6, 0.18], [0.36, 0.8, 0.58, 0.8, 0.5]].forEach(([dx, size, hue, , ], k) => {
      const c = hsv(hue, 0.75, 0.85), x0 = cx + dx * H * 0.5, bw = unit * (1.1 + size * 0.6), bh = unit * size;
      rect(x0, gy - bh, x0 + bw, gy + 1, c[0], c[1], c[2], true);
      rect(x0 + bw / 2 - 0.6, gy - bh, x0 + bw / 2 + 0.6, gy, 245, 215, 90, true);
      if (bh > 2.5) rect(x0, gy - bh / 2 - 0.5, x0 + bw, gy - bh / 2 + 0.5, 245, 215, 90, true);
      void k;
    });
    snow = new Snowfall(w, h, solid, rng, Math.max(20, Math.min(420, Math.floor(w * h / 70))));
  };
  return (s, t, dt) => {
    if (s.w !== w || s.h !== h) { w = s.w; h = s.h; if (w < 12 || h < 12) { snow = null; return; } build(); }
    if (!snow) return;
    const px = s.px;
    px.set(scene);
    for (const q of twinkles) { const v = 0.25 + 0.75 * (0.5 + 0.5 * Math.sin(t * 1.6 + q.ph)); s.set(q.x, q.y, 190 * v, 200 * v, 255 * v); }
    if (windowAt) { const f = 0.85 + 0.15 * Math.sin(t * 7) * Math.sin(t * 3.1); for (let dy = -2; dy <= 2; dy++) for (let dx = -3; dx <= 3; dx++) s.add(windowAt.x + dx, windowAt.y + dy, 28 * f / (1 + Math.hypot(dx, dy)), 18 * f / (1 + Math.hypot(dx, dy)), 4); }
    for (const b of baubles) { const c = hsv(b.hue, 0.85, 0.9); s.set(b.x, b.y, c[0], c[1], c[2]); s.set(b.x - 0.4, b.y - 0.9, 255, 255, 255); }
    const mode = Math.floor(t / 7) % 3;
    lights.forEach((l, i) => {
      const v = mode === 0 ? 0.5 + 0.5 * Math.sin(t * 2.4 + l.ph) : mode === 1 ? 0.5 + 0.5 * Math.sin(t * 4 - i * 0.7) : 0.5 + 0.5 * Math.sin(t * 1.5 + (i % 2) * Math.PI);
      const c = hsv(l.hue, 0.35, 1), b = 0.2 + 0.8 * v * v;
      s.set(l.x, l.y, c[0] * b, c[1] * b, c[2] * b);
      const g = 0.35 * b;
      s.add(l.x - 1, l.y, c[0] * g, c[1] * g, c[2] * g); s.add(l.x + 1, l.y, c[0] * g, c[1] * g, c[2] * g); s.add(l.x, l.y - 1, c[0] * g, c[1] * g, c[2] * g); s.add(l.x, l.y + 1, c[0] * g, c[1] * g, c[2] * g);
    });
    const sp = 0.7 + 0.3 * Math.sin(t * 3);
    for (let d = -2; d <= 2; d++) { const a = Math.max(0, 1 - Math.abs(d) / 2.5) * sp; s.add(star.x + d, star.y, 255 * a, 215 * a, 90 * a); s.add(star.x, star.y + d - 1, 255 * a, 215 * a, 90 * a); }
    snow.step(dt, t);
    const set = snow.settled;
    for (let i = 0; i < set.length; i++) if (set[i]) { px[i * 3] = 246; px[i * 3 + 1] = 249; px[i * 3 + 2] = 255; }
    for (const f of snow.flakes) { if (f.y < 0) continue; const v = 140 + 115 * f.d; s.set(f.x, f.y, v, v, 255); }
  };
}

function christmasLights(rng: Rng): Instance {
  type Flake = { x: number; y: number; layer: number; ph: number };
  let flakes: Flake[] = [], cols = 0, rows = 0;
  const messages = ["Merry Christmas", "and a happy new year"];
  const flakeGlyph = (layer: number, utf8: boolean) => layer === 0 ? "." : layer === 1 ? (utf8 ? "•" : "o") : "*";
  return (s, t, dt) => {
    if (s.cols !== cols || s.rows !== rows) {
      cols = s.cols; rows = s.rows;
      flakes = Array.from({ length: Math.max(10, Math.floor(cols * rows / 14)) }, () => ({ x: rng() * cols, y: rng() * rows, layer: Math.floor(rng() * 3), ph: rng() * TAU }));
    }
    const { w, h, px } = s;
    // Sky with a slow green and violet aurora.
    for (let y = 0; y < h; y++) {
      const k = y / h;
      for (let x = 0; x < w; x++) {
        const curtain = Math.sin(x * 0.06 + t * 0.25 + Math.sin(y * 0.04 + t * 0.15) * 2) * 0.5 + 0.5;
        const band = Math.exp(-Math.pow((k - 0.38 - 0.12 * Math.sin(x * 0.03 + t * 0.1)) / 0.2, 2)) * curtain;
        const p = (y * w + x) * 3;
        px[p] = 4 + 40 * band * band + 14 * k; px[p + 1] = 8 + 150 * band * band; px[p + 2] = 24 + 40 * k + 90 * band * band * (0.5 + 0.5 * Math.sin(x * 0.02 + t * 0.1));
      }
    }
    // Snowy ground.
    for (let y = Math.floor(h * 0.9); y < h; y++) for (let x = 0; x < w; x++) { const p = (y * w + x) * 3, k = (y - h * 0.9) / (h * 0.1); px[p] = 210 - 60 * k; px[p + 1] = 220 - 55 * k; px[p + 2] = 245 - 25 * k; }
    // Three festoons of lights. A wire, then bulbs that chase, alternate and sparkle.
    const mode = Math.floor(t / 6) % 3, spacing = Math.max(3, Math.round(h / 20));
    for (let str = 0; str < 3; str++) {
      const baseY = h * (0.1 + 0.2 * str), swags = Math.max(2, Math.round(w / (h * 0.9))), sag = h * 0.09;
      let bulb = 0;
      const segW = w / swags;
      for (let x = 0; x < w; x++) {
        const u = (x % segW) / segW, y = baseY + sag * 4 * u * (1 - u) + str * 0;
        s.set(x, y, 20, 48, 30);
        if (x % spacing === Math.floor(spacing / 2)) {
          const idx = bulb++ + str * 7;
          const v = mode === 0 ? 0.5 + 0.5 * Math.sin(t * 3 - idx * 0.5) : mode === 1 ? (Math.floor(t * 2 + idx) % 2 ? 1 : 0.18) : Math.pow(0.5 + 0.5 * Math.sin(t * 5 + idx * 12.9898), 3) + 0.12;
          const hueB = (idx * 0.17 + (mode === 0 ? t * 0.1 : 0)) % 1, c = hsv(hueB, 0.75, 1), b = 0.25 + 0.75 * clamp01(v);
          s.set(x, y + 1, c[0] * b, c[1] * b, c[2] * b);
          for (let dy = -2; dy <= 3; dy++) for (let dx = -2; dx <= 2; dx++) { const f = 0.35 * b / (1 + dx * dx + (dy - 1) * (dy - 1)); s.add(x + dx, y + dy, c[0] * f, c[1] * f, c[2] * f); }
        }
      }
    }
    // Snow in three depths, as glyphs.
    for (const f of flakes) {
      f.y += (3 + f.layer * 3.5) * dt; f.x += Math.sin(t * 1.1 + f.ph) * 1.5 * dt * (1 + f.layer);
      if (f.y >= rows) { f.y = -rng() * 3; f.x = rng() * cols; }
      if (f.x < 0) f.x += cols; else if (f.x >= cols) f.x -= cols;
      const v = 150 + f.layer * 50;
      s.put(f.x, f.y, flakeGlyph(f.layer, s.utf8), v, v, 255);
    }
    // The greeting, a letter at a time in a colour that moves along it.
    if (cols >= 20 && rows >= 10) {
      const msg = messages[Math.floor(t / 8) % messages.length], row = Math.floor(rows * 0.62), start = Math.floor((cols - msg.length) / 2);
      const fade = clamp01(Math.min((t % 8) * 2, (8 - (t % 8)) * 2));
      for (let i = 0; i < msg.length; i++) {
        if (msg[i] === " ") continue;
        const c = hsv(i * 0.06 + t * 0.15, 0.55, fade);
        s.put(start + i, row, msg[i], c[0] * 255 / 255, c[1], c[2]);
      }
      s.dim(row, 0.3 + 0.7 * (1 - fade));
    }
  };
}

// ---------------------------------------------------------------- the lists

/** The savers in normal rotation, in the order of the help screen. */
export const savers: Saver[] = [
  { name: "plasma", help: "Sine plasma in rainbow colour.", make: plasma },
  { name: "tunnel", help: "A chequered tunnel, flying down it.", make: tunnel },
  { name: "fire", help: "Flames rising from the bottom edge.", make: fire },
  { name: "rain", help: "Falling glyphs in rainbow columns.", make: rain },
  { name: "stars", help: "Stars flying towards you.", make: stars },
  { name: "life", help: "Conway's Game of Life on a torus; young cells white, old cells shift hue, the dead leave a glow.", make: life },
  { name: "snakes", help: "Snakes hunting dots on a wrapping board, growing as they eat, leaving colour trails.", make: snakes },
  { name: "sponge", help: "A rotating 3D Menger sponge, ray-cast and lit; a cube with square tunnels cut through it, repeatedly.", make: sponge },
  { name: "sponge4d", help: "4D Menger sponge turning in XW+YW; colour = W depth (red near, blue far)", make: sponge4d },
  { name: "lissajous", help: "Three Lissajous curves drawn with a phosphor glow that fades.", make: lissajous },
  { name: "metaballs", help: "Blobs that merge and part as their fields add.", make: metaballs },
  { name: "torus", help: "A spinning shaded torus with a specular highlight.", make: torus },
  { name: "waves", help: "Ripples from raindrops on water, spreading and reflecting from the edges.", make: waves },
  { name: "maze", help: "A maze is carved, then flooded in colour from the corner and solved.", make: maze },
  { name: "cyclic", help: "A cyclic cellular automaton: 14 states chase each other into nested bands.", make: cyclic },
];

/** Hidden: not in the help list nor the usual rotation. */
export const eggs: Saver[] = [
  { name: "xmas-tree", help: "A snowy night: a decorated tree with twinkling lights, a lit house, snow that settles.", egg: true, make: christmasTree },
  { name: "xmas-lights", help: "Strings of fairy lights under an aurora, and falling snow.", egg: true, make: christmasLights },
];
