// Small Canvas 2D scenes for the pixel test (canvas2d_test.ts; record
// docs/designissues/2026-11-08-canvas-2d.md). The same file runs in headless Chrome
// (canvas2d_reference.mjs, which writes canvas2d-reference.json) and in the Foafnaut engine
// on both script engines; the test compares the pixels. Each scene draws on a 48 x 48
// canvas. Text is not here: the fonts differ between the browsers.
const canvas2dScenes = [
  ['rects', c => { c.fillStyle = '#c33'; c.fillRect(4, 4, 30, 30); c.fillStyle = 'rgba(0, 0, 255, 0.5)'; c.fillRect(14, 14, 30, 30); }],
  ['nonzero', c => { c.fillStyle = 'teal'; c.beginPath(); c.moveTo(24, 2); c.lineTo(38, 46); c.lineTo(2, 18); c.lineTo(46, 18); c.lineTo(10, 46); c.closePath(); c.fill(); }],
  ['evenodd', c => { c.fillStyle = 'teal'; c.beginPath(); c.moveTo(24, 2); c.lineTo(38, 46); c.lineTo(2, 18); c.lineTo(46, 18); c.lineTo(10, 46); c.closePath(); c.fill('evenodd'); }],
  ['caps', c => { c.lineWidth = 8; ['butt', 'round', 'square'].forEach((cap, i) => { c.lineCap = cap; c.beginPath(); c.moveTo(10, 10 + i * 14); c.lineTo(38, 10 + i * 14); c.stroke(); }); }],
  ['joins', c => { c.lineWidth = 6; ['miter', 'round', 'bevel'].forEach((j, i) => { c.lineJoin = j; c.beginPath(); c.moveTo(4 + i * 15, 40); c.lineTo(10 + i * 15, 8); c.lineTo(16 + i * 15, 40); c.stroke(); }); }],
  ['dashes', c => { c.lineWidth = 3; c.setLineDash([6, 3]); c.lineDashOffset = 2; c.strokeRect(6, 6, 36, 36); c.beginPath(); c.moveTo(6, 24); c.lineTo(42, 24); c.stroke(); }],
  ['arcs', c => { c.fillStyle = '#3a6'; c.beginPath(); c.arc(16, 16, 12, 0, Math.PI * 1.5); c.lineTo(16, 16); c.fill(); c.strokeStyle = '#a36'; c.lineWidth = 2; c.beginPath(); c.ellipse(30, 32, 14, 8, 0.4, 0, Math.PI * 2); c.stroke(); }],
  ['curves', c => { c.fillStyle = '#25c'; c.beginPath(); c.moveTo(4, 40); c.bezierCurveTo(4, 0, 44, 0, 44, 40); c.quadraticCurveTo(24, 20, 4, 40); c.fill(); }],
  ['linear', c => { const g = c.createLinearGradient(0, 0, 48, 0); g.addColorStop(0, 'red'); g.addColorStop(0.5, 'yellow'); g.addColorStop(1, 'blue'); c.fillStyle = g; c.fillRect(0, 0, 48, 48); }],
  ['radial', c => { const g = c.createRadialGradient(20, 20, 2, 24, 24, 22); g.addColorStop(0, 'white'); g.addColorStop(1, 'rgba(0, 80, 0, 1)'); c.fillStyle = g; c.fillRect(0, 0, 48, 48); }],
  ['conic', c => { const g = c.createConicGradient(0.5, 24, 24); g.addColorStop(0, '#f00'); g.addColorStop(0.5, '#0f0'); g.addColorStop(1, '#f00'); c.fillStyle = g; c.fillRect(0, 0, 48, 48); }],
  ['pattern', c => { const p = document.createElement('canvas'); p.width = 8; p.height = 8; const pc = p.getContext('2d'); pc.fillStyle = '#ccc'; pc.fillRect(0, 0, 8, 8); pc.fillStyle = '#333'; pc.fillRect(0, 0, 4, 4); pc.fillRect(4, 4, 4, 4); c.fillStyle = c.createPattern(p, 'repeat'); c.fillRect(4, 4, 40, 40); }],
  ['transform', c => { c.translate(24, 24); c.rotate(Math.PI / 6); c.scale(1.5, 0.75); c.fillStyle = '#e80'; c.fillRect(-12, -12, 24, 24); }],
  ['clip', c => { c.beginPath(); c.arc(24, 24, 16, 0, Math.PI * 2); c.clip(); c.fillStyle = '#909'; c.fillRect(0, 0, 48, 30); c.fillStyle = '#099'; c.fillRect(0, 30, 48, 18); }],
  ['source-in', c => { c.fillStyle = 'blue'; c.fillRect(4, 4, 28, 28); c.globalCompositeOperation = 'source-in'; c.fillStyle = 'red'; c.fillRect(16, 16, 28, 28); }],
  ['destination-over', c => { c.fillStyle = 'blue'; c.fillRect(4, 4, 28, 28); c.globalCompositeOperation = 'destination-over'; c.fillStyle = 'red'; c.fillRect(16, 16, 28, 28); }],
  ['xor', c => { c.fillStyle = 'blue'; c.fillRect(4, 4, 28, 28); c.globalCompositeOperation = 'xor'; c.fillStyle = 'red'; c.fillRect(16, 16, 28, 28); }],
  ['multiply', c => { c.fillStyle = '#4af'; c.fillRect(4, 4, 28, 28); c.globalCompositeOperation = 'multiply'; c.fillStyle = '#fa4'; c.fillRect(16, 16, 28, 28); }],
  ['alpha', c => { c.globalAlpha = 0.4; c.fillStyle = 'black'; c.fillRect(0, 0, 32, 48); c.fillRect(16, 0, 32, 48); }],
  ['drawImage', c => { const s = document.createElement('canvas'); s.width = 12; s.height = 12; const sc = s.getContext('2d'); sc.fillStyle = 'red'; sc.fillRect(0, 0, 6, 12); sc.fillStyle = 'blue'; sc.fillRect(6, 0, 6, 12); c.imageSmoothingEnabled = false; c.drawImage(s, 4, 4, 40, 40); }],
  ['imageData', c => { const d = c.createImageData(16, 16); for (let i = 0; i < d.data.length; i += 4) { d.data[i] = i % 255; d.data[i + 1] = 128; d.data[i + 2] = 255 - i % 255; d.data[i + 3] = 255; } c.putImageData(d, 8, 8); c.putImageData(d, 28, 28, 4, 4, 8, 8); }],
  ['roundRect', c => { c.fillStyle = '#5a5'; c.beginPath(); c.roundRect(4, 4, 40, 28, [10, 4]); c.fill(); c.strokeStyle = '#000'; c.beginPath(); c.roundRect(8, 34, 32, 10, 5); c.stroke(); }],
  ['arcTo', c => { c.lineWidth = 4; c.beginPath(); c.moveTo(4, 44); c.arcTo(4, 4, 44, 4, 16); c.lineTo(44, 4); c.stroke(); }],
  ['clearRect', c => { c.fillStyle = '#333'; c.fillRect(0, 0, 48, 48); c.clearRect(10, 10, 20, 20); c.rotate(0.3); c.clearRect(30, 0, 10, 10); }],
  ['shadow', c => { c.shadowColor = 'rgba(0, 0, 0, 0.6)'; c.shadowOffsetX = 4; c.shadowOffsetY = 4; c.shadowBlur = 4; c.fillStyle = '#f80'; c.fillRect(8, 8, 26, 26); }],
  ['saveRestore', c => { c.fillStyle = 'red'; c.save(); c.fillStyle = 'green'; c.translate(10, 10); c.fillRect(0, 0, 20, 20); c.restore(); c.fillRect(30, 30, 14, 14); }],
  ['path2d', c => { const p = new Path2D('M4 4 L44 4 L24 44 Z'); c.fillStyle = '#36c'; c.fill(p); const q = new Path2D(); q.rect(18, 8, 12, 12); c.fillStyle = '#fc3'; c.fill(q); }],
];
