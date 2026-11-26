#!/usr/bin/env python3
"""Write pages/jukebox.html: a playlist page on the Web Audio API.

Issue https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut), stage E of
docs/designissues/2026-11-26-foafnaut-audio-plan.md. A `file:` page reads no other `file:` URL
(L4Factoidal.Net.PageFetch), so the clips are in the page: each CC0 clip of third_party/media
(made for this repository; licence and commands in its README) is a `script type="text/plain"`
element of base64 text, with its SHA-256 beside it. The page makes one more clip itself (a WAV).

Usage: python3 labs/demos/foafnaut/tools/jukebox-page.py   (Python standard library only)
"""
import base64
import hashlib
import html
import pathlib

LAB = pathlib.Path(__file__).resolve().parent.parent
MEDIA = LAB.parent.parent.parent / 'third_party' / 'media'
OUT = LAB / 'pages' / 'jukebox.html'

CLIPS = [
    ('arpeggio-cbr128.mp3', 'MP3, 128 kbit/s CBR, 44.1 kHz stereo'),
    ('arpeggio-vbr.mp3', 'MP3, VBR with a Xing/LAME header, 44.1 kHz stereo'),
    ('arpeggio-mono22.mp3', 'MP3 (MPEG-2), 48 kbit/s, 22.05 kHz mono'),
    ('arpeggio.ogg', 'Ogg Vorbis, 44.1 kHz stereo'),
    ('arpeggio.opus', 'Ogg Opus, 24 kbit/s, 48 kHz stereo'),
]

PAGE_HEAD = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Jukebox</title>
<!-- Written by labs/demos/foafnaut/tools/jukebox-page.py; do not edit by hand. -->
<style>
  :root { color-scheme: light dark; --fg: #1d1d1f; --bg: #f6f5f1; --muted: #5b5b5f; --line: #8a8a8e; --button: #ffffff; }
  @media (prefers-color-scheme: dark) { :root { --fg: #ececee; --bg: #1c1c1e; --muted: #a8a8ad; --line: #6c6c70; --button: #2c2c2e; } }
  body { font: 16px/1.45 system-ui, -apple-system, "Segoe UI", sans-serif; margin: 0; background: var(--bg); color: var(--fg); }
  main { max-width: 44rem; margin: 0 auto; padding: 1.5rem 1rem 3rem; }
  h1 { font-size: 1.6rem; margin: 0 0 0.25rem; }
  .note, .meta { color: var(--muted); font-size: 0.9rem; }
  .bar { display: flex; flex-wrap: wrap; gap: 0.5rem; align-items: center; margin: 0.75rem 0; }
  button { font: inherit; padding: 0.45rem 0.9rem; border: 1px solid var(--line); border-radius: 0.4rem; background: var(--button); color: inherit; }
  button[aria-pressed="true"] { background: var(--fg); color: var(--bg); }
  .slider { display: grid; grid-template-columns: 5.5rem 1fr; gap: 0.5rem; align-items: center; margin: 0.4rem 0; }
  input[type=range] { width: 100%; }
  #time, #status { font-variant-numeric: tabular-nums; }
  #status { min-height: 1.5em; }
  ol { padding-left: 1.6rem; }
  li { margin: 0.35rem 0; }
  li button { padding: 0.2rem 0.6rem; margin-right: 0.4rem; }
  li.current { font-weight: 600; }
</style>
</head>
<body>
<main>
<h1>Jukebox</h1>
<p class="note">Plays audio with the Web Audio API: <code>decodeAudioData</code>, <code>AudioBufferSourceNode</code>
and a <code>GainNode</code>. The five 4-second clips were made for this repository (CC0 1.0,
<code>third_party/media</code>), in MP3, Ogg Vorbis and Opus; this page makes the WAV itself. Open
audio files of your own with the file button.</p>
<div class="bar">
  <button id="prev" type="button">Previous</button>
  <button id="play" type="button">Play</button>
  <button id="next" type="button">Next</button>
  <button id="all" type="button" aria-pressed="false">Play all without gaps</button>
  <label><input id="repeat" type="checkbox"> Repeat</label>
</div>
<div class="slider"><label for="seek">Position</label><input id="seek" type="range" min="0" max="1" step="0.01" value="0"></div>
<div class="slider"><label for="vol">Volume</label><input id="vol" type="range" min="0" max="1" step="0.01" value="0.8"></div>
<p id="time">0:00.0 / 0:00.0</p>
<p id="status" role="status" aria-live="polite">Press Play.</p>
<div class="bar">
  <label>Open files <input id="files" type="file" accept="audio/*,.mp3,.ogg,.opus,.oga,.wav" multiple></label>
  <button id="decodeAll" type="button">Decode all</button>
</div>
<ol id="list"></ol>
<p class="meta" id="engine"></p>
<p class="meta" id="latency"></p>
</main>
"""

SCRIPT = r"""<script>
'use strict';
(function () {
  const $ = (id) => document.getElementById(id);
  const say = (text) => { $('status').textContent = text; };
  const fmt = (s) => {
    if (!(s >= 0) || !isFinite(s)) s = 0;
    const m = Math.floor(s / 60), r = s - 60 * m;
    return m + ':' + (r < 10 ? '0' : '') + r.toFixed(1);
  };
  const bytesOf = (b64) => {
    const s = atob(b64.replace(/\s+/g, ''));
    const u = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i);
    return u.buffer;
  };
  // A 2-second WAV made here: 16-bit PCM, 44.1 kHz stereo, an A minor chord with a decay.
  const makeWav = () => {
    const rate = 44100, n = 2 * rate, ch = 2, size = n * ch * 2;
    const d = new DataView(new ArrayBuffer(44 + size));
    const text = (o, s) => { for (let i = 0; i < s.length; i++) d.setUint8(o + i, s.charCodeAt(i)); };
    text(0, 'RIFF'); d.setUint32(4, 36 + size, true); text(8, 'WAVE');
    text(12, 'fmt '); d.setUint32(16, 16, true); d.setUint16(20, 1, true); d.setUint16(22, ch, true);
    d.setUint32(24, rate, true); d.setUint32(28, rate * ch * 2, true); d.setUint16(32, ch * 2, true);
    d.setUint16(34, 16, true); text(36, 'data'); d.setUint32(40, size, true);
    const hz = [220, 261.63, 329.63];
    for (let i = 0; i < n; i++) {
      const t = i / rate, env = Math.exp(-2 * t) * Math.min(1, t * 50);
      let l = 0, r = 0;
      for (let k = 0; k < 3; k++) {
        const v = Math.sin(2 * Math.PI * hz[k] * t) * env / 4;
        l += k === 2 ? 0.6 * v : v;
        r += k === 0 ? 0.6 * v : v;
      }
      d.setInt16(44 + 4 * i, Math.round(l * 32767), true);
      d.setInt16(46 + 4 * i, Math.round(r * 32767), true);
    }
    return d.buffer;
  };

  const tracks = [];
  for (const el of document.querySelectorAll('script[type="text/plain"][data-name]')) {
    tracks.push({ name: el.dataset.name, label: el.dataset.label, bytes: bytesOf(el.textContent) });
  }
  tracks.push({ name: 'a-minor-chord.wav', label: 'WAV, 16-bit PCM, 44.1 kHz stereo, made by this page', bytes: makeWav() });

  let ctx = null, gain = null;
  // The sources that are scheduled, in play order: {source, track, start (context time), offset, end}.
  let plan = [];
  let current = 0, pausedAt = 0, playing = false, gapless = false;
  let clickAt = 0, waitFirst = null;

  const audio = () => {
    if (!ctx) {
      const C = window.AudioContext || window.webkitAudioContext;
      if (!C) throw new Error('this browser has no AudioContext');
      ctx = new C({ latencyHint: 'playback' });
      gain = ctx.createGain();
      gain.gain.value = +$('vol').value;
      gain.connect(ctx.destination);
      $('engine').textContent = 'AudioContext: ' + ctx.sampleRate + ' Hz, ' + ctx.destination.maxChannelCount +
        ' output channels, base latency ' + ((ctx.baseLatency || 0) * 1000).toFixed(1) + ' ms, output latency ' +
        ((ctx.outputLatency || 0) * 1000).toFixed(1) + ' ms.';
    }
    if (ctx.state === 'suspended') ctx.resume().catch((e) => say('resume() failed: ' + e.message));
    return ctx;
  };

  const decode = (t) => {
    if (t.buffer) return Promise.resolve(t.buffer);
    if (!t.pending) {
      const t0 = performance.now();
      t.pending = audio().decodeAudioData(t.bytes.slice(0)).then((b) => {
        t.buffer = b; t.decodeMs = performance.now() - t0; drawList(); return b;
      }, (e) => {
        t.error = (e && e.name ? e.name + ': ' : '') + ((e && e.message) || String(e)); t.pending = null; drawList(); throw e;
      });
    }
    return t.pending;
  };

  const drawList = () => {
    const ol = $('list');
    ol.textContent = '';
    tracks.forEach((t, i) => {
      const li = document.createElement('li');
      if (i === current) li.className = 'current';
      const b = document.createElement('button');
      b.type = 'button'; b.textContent = 'Play'; b.setAttribute('aria-label', 'Play ' + t.name);
      b.addEventListener('click', () => start(i, 0));
      li.appendChild(b);
      li.appendChild(document.createTextNode(t.name + ' '));
      const meta = document.createElement('span');
      meta.className = 'meta';
      let m = t.label;
      if (t.buffer) m += '; ' + t.buffer.duration.toFixed(3) + ' s, ' + t.buffer.sampleRate + ' Hz, ' + t.buffer.numberOfChannels +
        ' ch, decoded in ' + t.decodeMs.toFixed(0) + ' ms';
      if (t.error) m += '; not decoded: ' + t.error;
      meta.textContent = m;
      li.appendChild(meta);
      ol.appendChild(li);
    });
  };

  const stopSources = () => {
    for (const p of plan) { p.source.onended = null; try { p.source.stop(); } catch (e) { /* never started */ } }
    plan = [];
  };

  // The entry of `plan` that plays at context time `now` (the last one that has started).
  const playingEntry = (now) => {
    let e = null;
    for (const p of plan) if (p.start <= now) e = p;
    return e;
  };

  const schedule = (i, offset, when) => {
    const t = tracks[i], src = ctx.createBufferSource();
    src.buffer = t.buffer;
    src.connect(gain);
    src.start(when, offset);
    const entry = { source: src, track: i, start: when, offset, end: when + t.buffer.duration - offset };
    // Only the last source scheduled ends a play: then the next track, the first again
    // (Repeat), or the end.
    src.onended = () => {
      if (!playing || plan[plan.length - 1] !== entry) return;
      if (i + 1 < tracks.length) start(i + 1, 0);
      else if ($('repeat').checked) start(0, 0);
      else { playing = false; pausedAt = 0; current = 0; plan = []; $('play').textContent = 'Play'; drawList(); say('Played to the end.'); }
    };
    plan.push(entry);
    return entry;
  };

  let generation = 0;
  const start = async (i, offset) => {
    const gen = ++generation;
    clickAt = performance.now();
    let c;
    try { c = audio(); } catch (e) { say('Cannot play: ' + e.message + '.'); return; }
    stopSources();
    current = (i + tracks.length) % tracks.length;
    playing = true;
    $('play').textContent = 'Pause';
    drawList();
    say('Decoding ' + tracks[current].name + ' ...');
    let k = current;
    try {
      await decode(tracks[k]);
      if (gapless) for (let j = k + 1; j < tracks.length; j++) await decode(tracks[j]);
    } catch (e) {
      if (gen !== generation) return;
      say('Cannot decode ' + tracks[k].name + ': ' + ((e && e.message) || e)); playing = false; $('play').textContent = 'Play'; return;
    }
    if (!playing || gen !== generation) return;
    let when = c.currentTime + 0.05;
    const first = schedule(k, Math.min(offset, tracks[k].buffer.duration), when);
    waitFirst = first.start;
    if (gapless) {
      let t = first.end;
      for (let j = k + 1; j < tracks.length; j++) { schedule(j, 0, t); t += tracks[j].buffer.duration; }
    }
    say('Playing ' + (k + 1) + ' of ' + tracks.length + ': ' + tracks[k].name + (gapless ? ', then the rest without gaps' : '') + '.');
  };

  const pause = () => {
    if (!ctx || !playing) return;
    const e = playingEntry(ctx.currentTime);
    pausedAt = e ? e.offset + (ctx.currentTime - e.start) : 0;
    if (e) current = e.track;
    playing = false;
    stopSources();
    $('play').textContent = 'Play';
    say('Paused at ' + fmt(pausedAt) + ' in ' + tracks[current].name + '.');
  };

  $('play').addEventListener('click', () => { if (playing) pause(); else start(current, pausedAt); });
  $('next').addEventListener('click', () => { pausedAt = 0; const e = ctx && playingEntry(ctx.currentTime); start((e ? e.track : current) + 1, 0); });
  $('prev').addEventListener('click', () => { pausedAt = 0; const e = ctx && playingEntry(ctx.currentTime); start((e ? e.track : current) - 1, 0); });
  $('all').addEventListener('click', () => {
    gapless = !gapless;
    $('all').setAttribute('aria-pressed', String(gapless));
    if (playing) { const e = playingEntry(ctx.currentTime); start(e ? e.track : current, e ? e.offset + (ctx.currentTime - e.start) : 0); }
  });
  $('vol').addEventListener('input', () => { if (gain) gain.gain.setTargetAtTime(+$('vol').value, ctx.currentTime, 0.02); });
  $('seek').addEventListener('change', () => {
    const t = tracks[current];
    if (!t.buffer) return;
    pausedAt = +$('seek').value * t.buffer.duration;
    if (playing) start(current, pausedAt);
  });
  $('decodeAll').addEventListener('click', async () => {
    try { audio(); } catch (e) { say('Cannot decode: ' + e.message + '.'); return; }
    let ok = 0;
    for (const t of tracks) { try { await decode(t); ok++; } catch (e) { /* shown in the list */ } }
    say('Decoded ' + ok + ' of ' + tracks.length + ' tracks.');
  });
  $('files').addEventListener('change', async () => {
    const files = Array.from($('files').files || []);
    for (const f of files) tracks.push({ name: f.name, label: (f.type || 'file') + ', ' + f.size + ' bytes, opened here', bytes: await f.arrayBuffer() });
    drawList();
    say(files.length + ' file(s) added.');
  });

  // The time line, ten times a second; and the delay from a click to the first frame heard, from
  // getOutputTimestamp() (the context time that the output device is playing now).
  setInterval(() => {
    if (!ctx) return;
    const now = ctx.currentTime;
    const e = playing ? playingEntry(now) : null;
    const i = e ? e.track : current;
    const t = tracks[i];
    const pos = e ? e.offset + (now - e.start) : pausedAt;
    const dur = t && t.buffer ? t.buffer.duration : 0;
    if (e && i !== current) { current = i; drawList(); say('Playing ' + (i + 1) + ' of ' + tracks.length + ': ' + t.name + '.'); }
    $('time').textContent = fmt(pos) + ' / ' + fmt(dur);
    if (dur > 0 && document.activeElement !== $('seek')) $('seek').value = String(Math.min(1, pos / dur));
    if (waitFirst !== null && ctx.getOutputTimestamp) {
      const ts = ctx.getOutputTimestamp();
      if (ts.contextTime >= waitFirst && ts.performanceTime > 0) {
        const heard = ts.performanceTime - (ts.contextTime - waitFirst) * 1000;
        $('latency').textContent = 'From the last click to the first frame played: about ' + Math.max(0, heard - clickAt).toFixed(0) + ' ms (getOutputTimestamp).';
        waitFirst = null;
      }
    }
  }, 100);

  drawList();
  window.jukebox = { tracks, decode, start, pause, state: () => ({ playing, current, gapless, plan: plan.length }) };
})();
</script>
"""


def main() -> None:
    parts = [PAGE_HEAD]
    for name, label in CLIPS:
        data = (MEDIA / name).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        b64 = base64.b64encode(data).decode('ascii')
        lines = '\n'.join(b64[i:i + 120] for i in range(0, len(b64), 120))
        parts.append(f'<script type="text/plain" data-name="{html.escape(name)}" data-label="{html.escape(label)}" '
                     f'data-sha256="{digest}">\n{lines}\n</script>\n')
    parts.append(SCRIPT)
    parts.append('</body>\n</html>\n')
    OUT.write_text(''.join(parts), encoding='utf-8')
    print(f'{OUT.relative_to(LAB.parent.parent.parent)}: {OUT.stat().st_size} bytes, {len(CLIPS)} clips')


if __name__ == '__main__':
    main()
